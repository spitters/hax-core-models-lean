
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! Operations of Rust `core` the extraction calls and the prelude does not define.
Overflow and division by zero fail as in a Rust debug build. `Impl_1` … `Impl_4`
are the inherent impls of `i16`, `i32`, `i64`, `i128`. -/

namespace Rust_primitives.Hax.Machine_int
def bitor {α} [OrOp α] (x y : α) : RustM α := pure (x ||| y)
end Rust_primitives.Hax.Machine_int

namespace Rust_primitives.Hax.Int
@[simp] def mul (x y : Hax_lib.Int.Int) : RustM Hax_lib.Int.Int := pure (x * y)
@[simp] def eq (x y : Hax_lib.Int.Int) : RustM Bool := pure (x == y)
end Rust_primitives.Hax.Int

namespace Core_models.Num.Impl_1
def MIN : i16 := Int16.minValue
def MAX : i16 := Int16.maxValue
def wrapping_add (x y : i16) : RustM i16 := pure (x + y)
def wrapping_sub (x y : i16) : RustM i16 := pure (x - y)
def overflowing_mul (x y : i16) : RustM (Rust_primitives.Hax.Tuple2 i16 Bool) :=
  pure ⟨x * y, decide (x.toInt * y.toInt ≠ (x * y).toInt)⟩
end Core_models.Num.Impl_1

namespace Core_models.Num.Impl_2
def MIN : i32 := Int32.minValue
def MAX : i32 := Int32.maxValue
def wrapping_add (x y : i32) : RustM i32 := pure (x + y)
def wrapping_sub (x y : i32) : RustM i32 := pure (x - y)
def overflowing_mul (x y : i32) : RustM (Rust_primitives.Hax.Tuple2 i32 Bool) :=
  pure ⟨x * y, decide (x.toInt * y.toInt ≠ (x * y).toInt)⟩
def abs (x : i32) : RustM i32 :=
  if x = Int32.minValue then .fail .integerOverflow
  else pure (if x < 0 then -x else x)
def rem_euclid (x y : i32) : RustM i32 :=
  if y = 0 then .fail .divisionByZero
  else if x = Int32.minValue ∧ y = -1 then .fail .integerOverflow
  else pure (Int32.ofInt (x.toInt % y.toInt))
end Core_models.Num.Impl_2

namespace Core_models.Num.Impl_3
def wrapping_add (x y : i64) : RustM i64 := pure (x + y)
end Core_models.Num.Impl_3

namespace Core_models.Num.Impl_4
def wrapping_sub (x y : i128) : RustM i128 := pure (x - y)
end Core_models.Num.Impl_4

/-- `b as T` for `b : bool`: `1` for `true`, `0` for `false`. -/
instance instCastBool {β : Type} [OfNat β 0] [OfNat β 1] : Cast Bool β where
  cast b := pure (if b then 1 else 0)

namespace Core_models.Num.Impl
def MIN : i8 := Int8.minValue
def MAX : i8 := Int8.maxValue
end Core_models.Num.Impl

namespace Rust_primitives.Hax.Int
@[simp] def add (x y : Hax_lib.Int.Int) : RustM Hax_lib.Int.Int := pure (x + y)
@[simp] def sub (x y : Hax_lib.Int.Int) : RustM Hax_lib.Int.Int := pure (x - y)
@[simp] def le (x y : Hax_lib.Int.Int) : RustM Bool := pure (decide (x ≤ y))
@[simp] def lt (x y : Hax_lib.Int.Int) : RustM Bool := pure (decide (x < y))
end Rust_primitives.Hax.Int

/-- `hax_lib::Int::_unsafe_from_str`: the integer a decimal literal denotes. -/
@[simp] def Hax_lib.Int.Impl_7._unsafe_from_str (s : String) : RustM Hax_lib.Int.Int :=
  pure s.toInt!

/-- `hax_lib::assert_prop`: a proof obligation with no run-time effect. -/
@[simp] def Hax_lib.assert_prop (_p : Prop) : RustM Rust_primitives.Hax.Tuple0 := pure ⟨⟩

/-! `as` casts to and from the 128-bit integers. The prelude represents both `i128` and
`u128` as `BitVec 128`, so a cast from a signed type sign-extends, a cast from an
unsigned type zero-extends, and a cast out of `BitVec 128` keeps the low bits. -/

instance instCastBV128Self : Cast (BitVec 128) (BitVec 128) where cast x := pure x
instance instCastU64BV128 : Cast u64 (BitVec 128) where cast x := pure (BitVec.ofNat 128 x.toNat)
instance instCastI64BV128 : Cast i64 (BitVec 128) where cast x := pure (BitVec.ofInt 128 x.toInt)
instance instCastI32BV128 : Cast i32 (BitVec 128) where cast x := pure (BitVec.ofInt 128 x.toInt)
instance instCastBV128U64 : Cast (BitVec 128) u64 where cast x := pure (UInt64.ofNat x.toNat)
instance instCastBV128I64 : Cast (BitVec 128) i64 where cast x := pure (Int64.ofInt x.toInt)
instance instCastBV128I32 : Cast (BitVec 128) i32 where cast x := pure (Int32.ofInt x.toInt)

@[reducible] instance instShrAssocBV128I32 : Core_models.Ops.Bit.Shr.AssociatedTypes (BitVec 128) i32 where
  Output := BitVec 128

/-- `u128 >> i32`: a logical shift; panics on a negative count or one of 128 or more. -/
instance instShrBV128I32 : Core_models.Ops.Bit.Shr (BitVec 128) i32 where
  shr x y := if 0 ≤ y && y < 128 then pure (x >>> y.toNatClampNeg) else .fail .integerOverflow


namespace Core_models.Abstractions.Bit

--  Represent a bit: `0` or `1`.
inductive Bit : Type
| Zero : Bit
| One : Bit

def Bit_discr (x : Bit) : RustM isize := do
  match x with
    | (Bit.Zero ) => (pure (0 : isize))
    | (Bit.One ) => (pure (1 : isize))

@[instance] opaque Impl_3.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  Core_models.Clone.Clone Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  Core_models.Marker.Copy Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  Core_models.Marker.StructuralPartialEq.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  Core_models.Marker.StructuralPartialEq Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  Core_models.Cmp.PartialEq.AssociatedTypes Bit Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  Core_models.Cmp.PartialEq Bit Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  Core_models.Cmp.Eq.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  Core_models.Cmp.Eq Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes :
  Core_models.Fmt.Debug.AssociatedTypes Bit :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7 :
  Core_models.Fmt.Debug Bit :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes Bool Bit
  where

instance Impl : Core_models.Convert.From Bool Bit where
  _from := fun (bit : Bit) => do
    match bit with | (Bit.Zero ) => (pure false) | (Bit.One ) => (pure true)

@[reducible] instance Impl_8.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u8 Bit
  where

instance Impl_8 : Core_models.Convert.From u8 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_9.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u16 Bit
  where

instance Impl_9 : Core_models.Convert.From u16 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_10.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u32 Bit
  where

instance Impl_10 : Core_models.Convert.From u32 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_11.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u64 Bit
  where

instance Impl_11 : Core_models.Convert.From u64 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_12.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes u128 Bit
  where

instance Impl_12 : Core_models.Convert.From u128 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_13.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i8 Bit
  where

instance Impl_13 : Core_models.Convert.From i8 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_14.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i16 Bit
  where

instance Impl_14 : Core_models.Convert.From i16 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_15.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i32 Bit
  where

instance Impl_15 : Core_models.Convert.From i32 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_16.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i64 Bit
  where

instance Impl_16 : Core_models.Convert.From i64 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_17.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes i128 Bit
  where

instance Impl_17 : Core_models.Convert.From i128 Bit where
  _from := fun (bit : Bit) => do
    (Rust_primitives.Hax.cast_op
      (← (Core_models.Convert.From._from Bool Bit bit)))

@[reducible] instance Impl_1.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes Bit Bool
  where

instance Impl_1 : Core_models.Convert.From Bit Bool where
  _from := fun (b : Bool) => do
    match b with | false => (pure Bit.Zero) | true => (pure Bit.One)

--  A trait for types that represent machine integers.
class MachineInteger.AssociatedTypes (Self : Type) where

class MachineInteger (Self : Type)
  [associatedTypes : outParam (MachineInteger.AssociatedTypes (Self : Type))]
  where
  bits (Self) : (Rust_primitives.Hax.Tuple0 -> RustM u32)
  SIGNED (Self) : Bool

def __2 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

end Core_models.Abstractions.Bit


namespace Core_models.Abstractions.Bitvec

def anon_const_1 : Rust_primitives.Hax.Tuple0 :=
  RustM.of_isOk (do Rust_primitives.Hax.Tuple0.mk) (by rfl)

--  An F* attribute that indiquates a rewritting lemma should be applied
def REWRITE_RULE : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

--  This function is useful only for verification in F*.
--  Used with `postprocess_rewrite`, this tactic:
--   1. Applies a series of rewrite rules (the lemmas marked with `REWRITE_RULE`)
--   2. Normalizes, bottom-up, every sub-expressions typed `BitVec<_>` inside the body of a function.
--  This tactic should be used on expressions that compute a _static_ permutation of bits.
def bitvec_postprocess_norm (_ : Rust_primitives.Hax.Tuple0) :
    RustM Rust_primitives.Hax.Tuple0 := do
  (pure Rust_primitives.Hax.Tuple0.mk)

end Core_models.Abstractions.Bitvec


namespace Core_models.Abstractions.Bitvec.Int_vec_interp

--  An F* attribute that marks an item as being an interpretation lemma.
def SIMPLIFICATION_LEMMA : Rust_primitives.Hax.Tuple0 :=
  RustM.of_isOk (do Rust_primitives.Hax.Tuple0.mk) (by rfl)

def anon_const_2 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __1 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __2 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __3 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __4 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __5 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __6 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __7 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __8 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __9 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __10 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __11 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __12 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __13 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __14 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

def __15 : Rust_primitives.Hax.Tuple0 := Rust_primitives.Hax.Tuple0.mk

--  Normalize `from` calls that convert from one type to itself
def __18 : Rust_primitives.Hax.Tuple0 :=
  RustM.of_isOk (do Rust_primitives.Hax.Tuple0.mk) (by rfl)

end Core_models.Abstractions.Bitvec.Int_vec_interp


namespace Core_models.Abstractions.Funarr

/-- `FunArray N T`: the Rust type stores a 512-slot array of `Option T` whose first
`N` slots are `some`; this model stores the same data as a function on indices. -/
structure FunArray (N : u64) (T : Type) where
  _0 : u64 → Core_models.Option.Option T

/-- `FunArray::get`: the element at `i`, panicking where the Rust `unwrap` panics. -/
def Impl_5.get (N : u64) (T : Type) (self : FunArray N T) (i : u64) : RustM T :=
  match self._0 i with
  | .Some v => pure v
  | .None => .fail .panic

/-- `FunArray::from_fn`: evaluates `f` at `0, …, N - 1` in order. -/
def Impl_5.from_fn (N : u64) (T : Type) (_F : Type) (f : u64 → RustM T) :
    RustM (FunArray N T) := do
  let xs ← (List.range N.toNat).mapM (fun i => f (UInt64.ofNat i))
  pure ⟨fun i => match xs[i.toNat]? with | some v => .Some v | none => .None⟩

/-- `FunArray::fold`: `init = f(init, self[i])` for `i` in `0..N`. -/
def Impl_5.fold (N : u64) (T : Type) (A : Type) (self : FunArray N T) (init : A)
    (f : A → T → RustM A) : RustM A :=
  (List.range N.toNat).foldlM
    (fun acc i => do f acc (← Impl_5.get N T self (UInt64.ofNat i))) init

/-- `impl Index<u64> for FunArray`: `self[i]` is `get`. -/
instance instGetElemResultU64 {N : u64} {T : Type} : GetElemResult (FunArray N T) u64 T where
  getElemResult a i := Impl_5.get N T a i

end Core_models.Abstractions.Funarr


namespace Core_models.Abstractions.Bitvec

--  A fixed-size bit vector type.
-- 
--  `BitVec<N>` is a specification-friendly, fixed-length bit vector that internally
--  stores an array of [`Bit`] values, where each `Bit` represents a single binary digit (0 or 1).
-- 
--  This type provides several utility methods for constructing and converting bit vectors:
-- 
--  The [`Debug`] implementation for `BitVec` pretty-prints the bits in groups of eight,
--  making the bit pattern more human-readable. The type also implements indexing,
--  allowing for easy access to individual bits.
structure BitVec (N : u64) where
  _0 :
    (Core_models.Abstractions.Funarr.FunArray
      (N)
      Core_models.Abstractions.Bit.Bit)

/-- `BitVec::from_fn`: `Self(FunArray::from_fn(f))`. -/
def Impl_9.from_fn (N : u64) (_F : Type) (f : u64 → RustM Core_models.Abstractions.Bit.Bit) :
    RustM (BitVec N) := do
  pure ⟨← Core_models.Abstractions.Funarr.Impl_5.from_fn N Core_models.Abstractions.Bit.Bit _F f⟩

/-- `impl Index<u64> for BitVec`: `self[i]` is `self.0[i]`. -/
instance instGetElemResultU64 {N : u64} : GetElemResult (BitVec N) u64 Core_models.Abstractions.Bit.Bit where
  getElemResult a i := Core_models.Abstractions.Funarr.Impl_5.get N Core_models.Abstractions.Bit.Bit a._0 i

@[instance] opaque Impl_1.AssociatedTypes (N : u64) :
  Core_models.Clone.Clone.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 (N : u64) :
  Core_models.Clone.Clone (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl.AssociatedTypes (N : u64) :
  Core_models.Marker.Copy.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl (N : u64) :
  Core_models.Marker.Copy (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes (N : u64) :
  Core_models.Marker.StructuralPartialEq.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 (N : u64) :
  Core_models.Marker.StructuralPartialEq (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes (N : u64) :
  Core_models.Cmp.PartialEq.AssociatedTypes (BitVec (N)) (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 (N : u64) :
  Core_models.Cmp.PartialEq (BitVec (N)) (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes (N : u64) :
  Core_models.Cmp.Eq.AssociatedTypes (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 (N : u64) :
  Core_models.Cmp.Eq (BitVec (N)) :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl_6.AssociatedTypes (N : u64) :
  Core_models.Ops.Index.Index.AssociatedTypes (BitVec (N)) u64
  where
  Output := Core_models.Abstractions.Bit.Bit

instance Impl_6 (N : u64) : Core_models.Ops.Index.Index (BitVec (N)) u64 where
  index := fun (self : (BitVec (N))) (index : u64) => do
    (Core_models.Abstractions.Funarr.Impl_5.get
      (N)
      Core_models.Abstractions.Bit.Bit (BitVec._0 self) index)

def Impl_7.pointwise (self : (BitVec ((128 : u64)))) :
    RustM (BitVec ((128 : u64))) := do
  (Impl_9.from_fn ((128 : u64)) (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      match i with
        | 0 => self[(0 : u64)]_?
        | 1 => self[(1 : u64)]_?
        | 2 => self[(2 : u64)]_?
        | 3 => self[(3 : u64)]_?
        | 4 => self[(4 : u64)]_?
        | 5 => self[(5 : u64)]_?
        | 6 => self[(6 : u64)]_?
        | 7 => self[(7 : u64)]_?
        | 8 => self[(8 : u64)]_?
        | 9 => self[(9 : u64)]_?
        | 10 => self[(10 : u64)]_?
        | 11 => self[(11 : u64)]_?
        | 12 => self[(12 : u64)]_?
        | 13 => self[(13 : u64)]_?
        | 14 => self[(14 : u64)]_?
        | 15 => self[(15 : u64)]_?
        | 16 => self[(16 : u64)]_?
        | 17 => self[(17 : u64)]_?
        | 18 => self[(18 : u64)]_?
        | 19 => self[(19 : u64)]_?
        | 20 => self[(20 : u64)]_?
        | 21 => self[(21 : u64)]_?
        | 22 => self[(22 : u64)]_?
        | 23 => self[(23 : u64)]_?
        | 24 => self[(24 : u64)]_?
        | 25 => self[(25 : u64)]_?
        | 26 => self[(26 : u64)]_?
        | 27 => self[(27 : u64)]_?
        | 28 => self[(28 : u64)]_?
        | 29 => self[(29 : u64)]_?
        | 30 => self[(30 : u64)]_?
        | 31 => self[(31 : u64)]_?
        | 32 => self[(32 : u64)]_?
        | 33 => self[(33 : u64)]_?
        | 34 => self[(34 : u64)]_?
        | 35 => self[(35 : u64)]_?
        | 36 => self[(36 : u64)]_?
        | 37 => self[(37 : u64)]_?
        | 38 => self[(38 : u64)]_?
        | 39 => self[(39 : u64)]_?
        | 40 => self[(40 : u64)]_?
        | 41 => self[(41 : u64)]_?
        | 42 => self[(42 : u64)]_?
        | 43 => self[(43 : u64)]_?
        | 44 => self[(44 : u64)]_?
        | 45 => self[(45 : u64)]_?
        | 46 => self[(46 : u64)]_?
        | 47 => self[(47 : u64)]_?
        | 48 => self[(48 : u64)]_?
        | 49 => self[(49 : u64)]_?
        | 50 => self[(50 : u64)]_?
        | 51 => self[(51 : u64)]_?
        | 52 => self[(52 : u64)]_?
        | 53 => self[(53 : u64)]_?
        | 54 => self[(54 : u64)]_?
        | 55 => self[(55 : u64)]_?
        | 56 => self[(56 : u64)]_?
        | 57 => self[(57 : u64)]_?
        | 58 => self[(58 : u64)]_?
        | 59 => self[(59 : u64)]_?
        | 60 => self[(60 : u64)]_?
        | 61 => self[(61 : u64)]_?
        | 62 => self[(62 : u64)]_?
        | 63 => self[(63 : u64)]_?
        | 64 => self[(64 : u64)]_?
        | 65 => self[(65 : u64)]_?
        | 66 => self[(66 : u64)]_?
        | 67 => self[(67 : u64)]_?
        | 68 => self[(68 : u64)]_?
        | 69 => self[(69 : u64)]_?
        | 70 => self[(70 : u64)]_?
        | 71 => self[(71 : u64)]_?
        | 72 => self[(72 : u64)]_?
        | 73 => self[(73 : u64)]_?
        | 74 => self[(74 : u64)]_?
        | 75 => self[(75 : u64)]_?
        | 76 => self[(76 : u64)]_?
        | 77 => self[(77 : u64)]_?
        | 78 => self[(78 : u64)]_?
        | 79 => self[(79 : u64)]_?
        | 80 => self[(80 : u64)]_?
        | 81 => self[(81 : u64)]_?
        | 82 => self[(82 : u64)]_?
        | 83 => self[(83 : u64)]_?
        | 84 => self[(84 : u64)]_?
        | 85 => self[(85 : u64)]_?
        | 86 => self[(86 : u64)]_?
        | 87 => self[(87 : u64)]_?
        | 88 => self[(88 : u64)]_?
        | 89 => self[(89 : u64)]_?
        | 90 => self[(90 : u64)]_?
        | 91 => self[(91 : u64)]_?
        | 92 => self[(92 : u64)]_?
        | 93 => self[(93 : u64)]_?
        | 94 => self[(94 : u64)]_?
        | 95 => self[(95 : u64)]_?
        | 96 => self[(96 : u64)]_?
        | 97 => self[(97 : u64)]_?
        | 98 => self[(98 : u64)]_?
        | 99 => self[(99 : u64)]_?
        | 100 => self[(100 : u64)]_?
        | 101 => self[(101 : u64)]_?
        | 102 => self[(102 : u64)]_?
        | 103 => self[(103 : u64)]_?
        | 104 => self[(104 : u64)]_?
        | 105 => self[(105 : u64)]_?
        | 106 => self[(106 : u64)]_?
        | 107 => self[(107 : u64)]_?
        | 108 => self[(108 : u64)]_?
        | 109 => self[(109 : u64)]_?
        | 110 => self[(110 : u64)]_?
        | 111 => self[(111 : u64)]_?
        | 112 => self[(112 : u64)]_?
        | 113 => self[(113 : u64)]_?
        | 114 => self[(114 : u64)]_?
        | 115 => self[(115 : u64)]_?
        | 116 => self[(116 : u64)]_?
        | 117 => self[(117 : u64)]_?
        | 118 => self[(118 : u64)]_?
        | 119 => self[(119 : u64)]_?
        | 120 => self[(120 : u64)]_?
        | 121 => self[(121 : u64)]_?
        | 122 => self[(122 : u64)]_?
        | 123 => self[(123 : u64)]_?
        | 124 => self[(124 : u64)]_?
        | 125 => self[(125 : u64)]_?
        | 126 => self[(126 : u64)]_?
        | 127 => self[(127 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM Core_models.Abstractions.Bit.Bit)))

def Impl_8.pointwise (self : (BitVec ((256 : u64)))) :
    RustM (BitVec ((256 : u64))) := do
  (Impl_9.from_fn ((256 : u64)) (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      match i with
        | 0 => self[(0 : u64)]_?
        | 1 => self[(1 : u64)]_?
        | 2 => self[(2 : u64)]_?
        | 3 => self[(3 : u64)]_?
        | 4 => self[(4 : u64)]_?
        | 5 => self[(5 : u64)]_?
        | 6 => self[(6 : u64)]_?
        | 7 => self[(7 : u64)]_?
        | 8 => self[(8 : u64)]_?
        | 9 => self[(9 : u64)]_?
        | 10 => self[(10 : u64)]_?
        | 11 => self[(11 : u64)]_?
        | 12 => self[(12 : u64)]_?
        | 13 => self[(13 : u64)]_?
        | 14 => self[(14 : u64)]_?
        | 15 => self[(15 : u64)]_?
        | 16 => self[(16 : u64)]_?
        | 17 => self[(17 : u64)]_?
        | 18 => self[(18 : u64)]_?
        | 19 => self[(19 : u64)]_?
        | 20 => self[(20 : u64)]_?
        | 21 => self[(21 : u64)]_?
        | 22 => self[(22 : u64)]_?
        | 23 => self[(23 : u64)]_?
        | 24 => self[(24 : u64)]_?
        | 25 => self[(25 : u64)]_?
        | 26 => self[(26 : u64)]_?
        | 27 => self[(27 : u64)]_?
        | 28 => self[(28 : u64)]_?
        | 29 => self[(29 : u64)]_?
        | 30 => self[(30 : u64)]_?
        | 31 => self[(31 : u64)]_?
        | 32 => self[(32 : u64)]_?
        | 33 => self[(33 : u64)]_?
        | 34 => self[(34 : u64)]_?
        | 35 => self[(35 : u64)]_?
        | 36 => self[(36 : u64)]_?
        | 37 => self[(37 : u64)]_?
        | 38 => self[(38 : u64)]_?
        | 39 => self[(39 : u64)]_?
        | 40 => self[(40 : u64)]_?
        | 41 => self[(41 : u64)]_?
        | 42 => self[(42 : u64)]_?
        | 43 => self[(43 : u64)]_?
        | 44 => self[(44 : u64)]_?
        | 45 => self[(45 : u64)]_?
        | 46 => self[(46 : u64)]_?
        | 47 => self[(47 : u64)]_?
        | 48 => self[(48 : u64)]_?
        | 49 => self[(49 : u64)]_?
        | 50 => self[(50 : u64)]_?
        | 51 => self[(51 : u64)]_?
        | 52 => self[(52 : u64)]_?
        | 53 => self[(53 : u64)]_?
        | 54 => self[(54 : u64)]_?
        | 55 => self[(55 : u64)]_?
        | 56 => self[(56 : u64)]_?
        | 57 => self[(57 : u64)]_?
        | 58 => self[(58 : u64)]_?
        | 59 => self[(59 : u64)]_?
        | 60 => self[(60 : u64)]_?
        | 61 => self[(61 : u64)]_?
        | 62 => self[(62 : u64)]_?
        | 63 => self[(63 : u64)]_?
        | 64 => self[(64 : u64)]_?
        | 65 => self[(65 : u64)]_?
        | 66 => self[(66 : u64)]_?
        | 67 => self[(67 : u64)]_?
        | 68 => self[(68 : u64)]_?
        | 69 => self[(69 : u64)]_?
        | 70 => self[(70 : u64)]_?
        | 71 => self[(71 : u64)]_?
        | 72 => self[(72 : u64)]_?
        | 73 => self[(73 : u64)]_?
        | 74 => self[(74 : u64)]_?
        | 75 => self[(75 : u64)]_?
        | 76 => self[(76 : u64)]_?
        | 77 => self[(77 : u64)]_?
        | 78 => self[(78 : u64)]_?
        | 79 => self[(79 : u64)]_?
        | 80 => self[(80 : u64)]_?
        | 81 => self[(81 : u64)]_?
        | 82 => self[(82 : u64)]_?
        | 83 => self[(83 : u64)]_?
        | 84 => self[(84 : u64)]_?
        | 85 => self[(85 : u64)]_?
        | 86 => self[(86 : u64)]_?
        | 87 => self[(87 : u64)]_?
        | 88 => self[(88 : u64)]_?
        | 89 => self[(89 : u64)]_?
        | 90 => self[(90 : u64)]_?
        | 91 => self[(91 : u64)]_?
        | 92 => self[(92 : u64)]_?
        | 93 => self[(93 : u64)]_?
        | 94 => self[(94 : u64)]_?
        | 95 => self[(95 : u64)]_?
        | 96 => self[(96 : u64)]_?
        | 97 => self[(97 : u64)]_?
        | 98 => self[(98 : u64)]_?
        | 99 => self[(99 : u64)]_?
        | 100 => self[(100 : u64)]_?
        | 101 => self[(101 : u64)]_?
        | 102 => self[(102 : u64)]_?
        | 103 => self[(103 : u64)]_?
        | 104 => self[(104 : u64)]_?
        | 105 => self[(105 : u64)]_?
        | 106 => self[(106 : u64)]_?
        | 107 => self[(107 : u64)]_?
        | 108 => self[(108 : u64)]_?
        | 109 => self[(109 : u64)]_?
        | 110 => self[(110 : u64)]_?
        | 111 => self[(111 : u64)]_?
        | 112 => self[(112 : u64)]_?
        | 113 => self[(113 : u64)]_?
        | 114 => self[(114 : u64)]_?
        | 115 => self[(115 : u64)]_?
        | 116 => self[(116 : u64)]_?
        | 117 => self[(117 : u64)]_?
        | 118 => self[(118 : u64)]_?
        | 119 => self[(119 : u64)]_?
        | 120 => self[(120 : u64)]_?
        | 121 => self[(121 : u64)]_?
        | 122 => self[(122 : u64)]_?
        | 123 => self[(123 : u64)]_?
        | 124 => self[(124 : u64)]_?
        | 125 => self[(125 : u64)]_?
        | 126 => self[(126 : u64)]_?
        | 127 => self[(127 : u64)]_?
        | 128 => self[(128 : u64)]_?
        | 129 => self[(129 : u64)]_?
        | 130 => self[(130 : u64)]_?
        | 131 => self[(131 : u64)]_?
        | 132 => self[(132 : u64)]_?
        | 133 => self[(133 : u64)]_?
        | 134 => self[(134 : u64)]_?
        | 135 => self[(135 : u64)]_?
        | 136 => self[(136 : u64)]_?
        | 137 => self[(137 : u64)]_?
        | 138 => self[(138 : u64)]_?
        | 139 => self[(139 : u64)]_?
        | 140 => self[(140 : u64)]_?
        | 141 => self[(141 : u64)]_?
        | 142 => self[(142 : u64)]_?
        | 143 => self[(143 : u64)]_?
        | 144 => self[(144 : u64)]_?
        | 145 => self[(145 : u64)]_?
        | 146 => self[(146 : u64)]_?
        | 147 => self[(147 : u64)]_?
        | 148 => self[(148 : u64)]_?
        | 149 => self[(149 : u64)]_?
        | 150 => self[(150 : u64)]_?
        | 151 => self[(151 : u64)]_?
        | 152 => self[(152 : u64)]_?
        | 153 => self[(153 : u64)]_?
        | 154 => self[(154 : u64)]_?
        | 155 => self[(155 : u64)]_?
        | 156 => self[(156 : u64)]_?
        | 157 => self[(157 : u64)]_?
        | 158 => self[(158 : u64)]_?
        | 159 => self[(159 : u64)]_?
        | 160 => self[(160 : u64)]_?
        | 161 => self[(161 : u64)]_?
        | 162 => self[(162 : u64)]_?
        | 163 => self[(163 : u64)]_?
        | 164 => self[(164 : u64)]_?
        | 165 => self[(165 : u64)]_?
        | 166 => self[(166 : u64)]_?
        | 167 => self[(167 : u64)]_?
        | 168 => self[(168 : u64)]_?
        | 169 => self[(169 : u64)]_?
        | 170 => self[(170 : u64)]_?
        | 171 => self[(171 : u64)]_?
        | 172 => self[(172 : u64)]_?
        | 173 => self[(173 : u64)]_?
        | 174 => self[(174 : u64)]_?
        | 175 => self[(175 : u64)]_?
        | 176 => self[(176 : u64)]_?
        | 177 => self[(177 : u64)]_?
        | 178 => self[(178 : u64)]_?
        | 179 => self[(179 : u64)]_?
        | 180 => self[(180 : u64)]_?
        | 181 => self[(181 : u64)]_?
        | 182 => self[(182 : u64)]_?
        | 183 => self[(183 : u64)]_?
        | 184 => self[(184 : u64)]_?
        | 185 => self[(185 : u64)]_?
        | 186 => self[(186 : u64)]_?
        | 187 => self[(187 : u64)]_?
        | 188 => self[(188 : u64)]_?
        | 189 => self[(189 : u64)]_?
        | 190 => self[(190 : u64)]_?
        | 191 => self[(191 : u64)]_?
        | 192 => self[(192 : u64)]_?
        | 193 => self[(193 : u64)]_?
        | 194 => self[(194 : u64)]_?
        | 195 => self[(195 : u64)]_?
        | 196 => self[(196 : u64)]_?
        | 197 => self[(197 : u64)]_?
        | 198 => self[(198 : u64)]_?
        | 199 => self[(199 : u64)]_?
        | 200 => self[(200 : u64)]_?
        | 201 => self[(201 : u64)]_?
        | 202 => self[(202 : u64)]_?
        | 203 => self[(203 : u64)]_?
        | 204 => self[(204 : u64)]_?
        | 205 => self[(205 : u64)]_?
        | 206 => self[(206 : u64)]_?
        | 207 => self[(207 : u64)]_?
        | 208 => self[(208 : u64)]_?
        | 209 => self[(209 : u64)]_?
        | 210 => self[(210 : u64)]_?
        | 211 => self[(211 : u64)]_?
        | 212 => self[(212 : u64)]_?
        | 213 => self[(213 : u64)]_?
        | 214 => self[(214 : u64)]_?
        | 215 => self[(215 : u64)]_?
        | 216 => self[(216 : u64)]_?
        | 217 => self[(217 : u64)]_?
        | 218 => self[(218 : u64)]_?
        | 219 => self[(219 : u64)]_?
        | 220 => self[(220 : u64)]_?
        | 221 => self[(221 : u64)]_?
        | 222 => self[(222 : u64)]_?
        | 223 => self[(223 : u64)]_?
        | 224 => self[(224 : u64)]_?
        | 225 => self[(225 : u64)]_?
        | 226 => self[(226 : u64)]_?
        | 227 => self[(227 : u64)]_?
        | 228 => self[(228 : u64)]_?
        | 229 => self[(229 : u64)]_?
        | 230 => self[(230 : u64)]_?
        | 231 => self[(231 : u64)]_?
        | 232 => self[(232 : u64)]_?
        | 233 => self[(233 : u64)]_?
        | 234 => self[(234 : u64)]_?
        | 235 => self[(235 : u64)]_?
        | 236 => self[(236 : u64)]_?
        | 237 => self[(237 : u64)]_?
        | 238 => self[(238 : u64)]_?
        | 239 => self[(239 : u64)]_?
        | 240 => self[(240 : u64)]_?
        | 241 => self[(241 : u64)]_?
        | 242 => self[(242 : u64)]_?
        | 243 => self[(243 : u64)]_?
        | 244 => self[(244 : u64)]_?
        | 245 => self[(245 : u64)]_?
        | 246 => self[(246 : u64)]_?
        | 247 => self[(247 : u64)]_?
        | 248 => self[(248 : u64)]_?
        | 249 => self[(249 : u64)]_?
        | 250 => self[(250 : u64)]_?
        | 251 => self[(251 : u64)]_?
        | 252 => self[(252 : u64)]_?
        | 253 => self[(253 : u64)]_?
        | 254 => self[(254 : u64)]_?
        | 255 => self[(255 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM Core_models.Abstractions.Bit.Bit)))

--  Folds over the array, accumulating a result.
-- 
--  # Arguments
--  * `init` - The initial value of the accumulator.
--  * `f` - A function combining the accumulator and each element.
def Impl_10.fold (N : u64) (A : Type)
    (self : (BitVec (N)))
    (init : A)
    (f : (A -> Core_models.Abstractions.Bit.Bit -> RustM A)) :
    RustM A := do
  (Core_models.Abstractions.Funarr.Impl_5.fold
    (N)
    Core_models.Abstractions.Bit.Bit
    A (BitVec._0 self) init f)

end Core_models.Abstractions.Bitvec


namespace Core_models.Abstractions.Bitvec.Int_vec_interp

-- i32 vectors of size 8
abbrev i32x8 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)

-- Conversion from i32 vectors of size 8to  bit vectors of size 256
opaque Anon_0.Impl.from_i32x8
    (iv : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to i32 vectors of size 8
opaque Anon_0.Impl.to_i32x8
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) 

-- i64 vectors of size 4
abbrev i64x4 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)

-- Conversion from i64 vectors of size 4to  bit vectors of size 256
opaque Anon_1.Impl.from_i64x4
    (iv : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to i64 vectors of size 4
opaque Anon_1.Impl.to_i64x4
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) 

-- i16 vectors of size 16
abbrev i16x16 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)

-- Conversion from i16 vectors of size 16to  bit vectors of size 256
opaque Anon_2.Impl.from_i16x16
    (iv : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to i16 vectors of size 16
opaque Anon_2.Impl.to_i16x16
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) 

-- i128 vectors of size 2
abbrev i128x2 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128)

-- Conversion from i128 vectors of size 2to  bit vectors of size 256
opaque Anon_3.Impl.from_i128x2
    (iv : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to i128 vectors of size 2
opaque Anon_3.Impl.to_i128x2
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128) 

-- i8 vectors of size 32
abbrev i8x32 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((32 : u64)) i8)

-- Conversion from i8 vectors of size 32to  bit vectors of size 256
opaque Anon_4.Impl.from_i8x32
    (iv : (Core_models.Abstractions.Funarr.FunArray ((32 : u64)) i8)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to i8 vectors of size 32
opaque Anon_4.Impl.to_i8x32
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((32 : u64)) i8) 

-- u32 vectors of size 8
abbrev u32x8 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u32)

-- Conversion from u32 vectors of size 8to  bit vectors of size 256
opaque Anon_5.Impl.from_u32x8
    (iv : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u32)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to u32 vectors of size 8
opaque Anon_5.Impl.to_u32x8
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u32) 

-- u64 vectors of size 4
abbrev u64x4 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u64)

-- Conversion from u64 vectors of size 4to  bit vectors of size 256
opaque Anon_6.Impl.from_u64x4
    (iv : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u64)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to u64 vectors of size 4
opaque Anon_6.Impl.to_u64x4
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u64) 

-- u16 vectors of size 16
abbrev u16x16 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) u16)

-- Conversion from u16 vectors of size 16to  bit vectors of size 256
opaque Anon_7.Impl.from_u16x16
    (iv : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) u16)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

-- Conversion from bit vectors of size 256 to u16 vectors of size 16
opaque Anon_7.Impl.to_u16x16
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) u16) 

-- i32 vectors of size 4
abbrev i32x4 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i32)

-- Conversion from i32 vectors of size 4to  bit vectors of size 128
opaque Anon_8.Impl.from_i32x4
    (iv : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i32)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to i32 vectors of size 4
opaque Anon_8.Impl.to_i32x4
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i32) 

-- i64 vectors of size 2
abbrev i64x2 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i64)

-- Conversion from i64 vectors of size 2to  bit vectors of size 128
opaque Anon_9.Impl.from_i64x2
    (iv : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i64)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to i64 vectors of size 2
opaque Anon_9.Impl.to_i64x2
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i64) 

-- i16 vectors of size 8
abbrev i16x8 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)

-- Conversion from i16 vectors of size 8to  bit vectors of size 128
opaque Anon_10.Impl.from_i16x8
    (iv : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to i16 vectors of size 8
opaque Anon_10.Impl.to_i16x8
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16) 

-- i128 vectors of size 1
abbrev i128x1 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((1 : u64)) i128)

-- Conversion from i128 vectors of size 1to  bit vectors of size 128
opaque Anon_11.Impl.from_i128x1
    (iv : (Core_models.Abstractions.Funarr.FunArray ((1 : u64)) i128)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to i128 vectors of size 1
opaque Anon_11.Impl.to_i128x1
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((1 : u64)) i128) 

-- i8 vectors of size 16
abbrev i8x16 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i8)

-- Conversion from i8 vectors of size 16to  bit vectors of size 128
opaque Anon_12.Impl.from_i8x16
    (iv : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i8)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to i8 vectors of size 16
opaque Anon_12.Impl.to_i8x16
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i8) 

-- u32 vectors of size 4
abbrev u32x4 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u32)

-- Conversion from u32 vectors of size 4to  bit vectors of size 128
opaque Anon_13.Impl.from_u32x4
    (iv : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u32)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to u32 vectors of size 4
opaque Anon_13.Impl.to_u32x4
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u32) 

-- u64 vectors of size 2
abbrev u64x2 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) u64)

-- Conversion from u64 vectors of size 2to  bit vectors of size 128
opaque Anon_14.Impl.from_u64x2
    (iv : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) u64)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to u64 vectors of size 2
opaque Anon_14.Impl.to_u64x2
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) u64) 

-- u16 vectors of size 8
abbrev u16x8 :
  Type :=
  (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u16)

-- Conversion from u16 vectors of size 8to  bit vectors of size 128
opaque Anon_15.Impl.from_u16x8
    (iv : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u16)) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

-- Conversion from bit vectors of size 128 to u16 vectors of size 8
opaque Anon_15.Impl.to_u16x8
    (bv : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u16) 

def Impl.into_i32x8
    (self : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let value : i64 ←
        (Core_models.Abstractions.Funarr.Impl_5.get ((4 : u64)) i64
          self
          (← (i /? (2 : u64))));
      (Rust_primitives.Hax.cast_op
        (← if
        (← (Rust_primitives.Hax.Machine_int.eq (← (i %? (2 : u64))) (0 : u64)))
        then
          (pure value)
        else
          (value >>>? (32 : i32)))) :
      RustM i32)))

def Impl_1.into_i64x4
    (self : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      let low : u64 ←
        (Rust_primitives.Hax.cast_op
          (← (Rust_primitives.Hax.cast_op (β := u32)
            (← (Core_models.Abstractions.Funarr.Impl_5.get ((8 : u64)) i32
              self
              (← ((2 : u64) *? i)))))));
      let high : i64 ←
        (Rust_primitives.Hax.cast_op
          (← (Core_models.Abstractions.Funarr.Impl_5.get ((8 : u64)) i32
            self
            (← ((← ((2 : u64) *? i)) +? (1 : u64))))));
      (Rust_primitives.Hax.Machine_int.bitor
        (← (high <<<? (32 : i32)))
        (← (Rust_primitives.Hax.cast_op low))) :
      RustM i64)))

@[reducible] instance Impl_2.AssociatedTypes :
  Core_models.Convert.From.AssociatedTypes
  (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)
  (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)
  where

instance Impl_2 :
  Core_models.Convert.From
  (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)
  (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)
  where
  _from :=
    fun (vec : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) => do
    (Impl.into_i32x8 vec)

--  Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
--  yields the same result as directly converting the `i64x4` into an `i32x8`.
opaque lemma_rewrite_i64x4_bv_i32x8
    (bv : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM Rust_primitives.Hax.Tuple0 

--  Lemma stating that converting an `i64x4` vector to a `BitVec<256>` and then into an `i32x8`
--  yields the same result as directly converting the `i64x4` into an `i32x8`.
opaque lemma_rewrite_i32x8_bv_i64x4
    (bv : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Abstractions.Bitvec.Int_vec_interp


namespace Core_models.Abstractions.Funarr

@[instance] opaque Impl_1.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : Core_models.Clone.Clone T ] :
  Core_models.Clone.Clone.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (N : u64)
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    Core_models.Clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : Core_models.Clone.Clone T ] :
  Core_models.Clone.Clone (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    Core_models.Marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : Core_models.Marker.Copy T ] :
  Core_models.Marker.Copy.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl
  (N : u64)
  (T : Type)
  [trait_constr_Impl_associated_type_i0 :
    Core_models.Marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_i0 : Core_models.Marker.Copy T ] :
  Core_models.Marker.Copy (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes (N : u64) (T : Type) :
  Core_models.Marker.StructuralPartialEq.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 (N : u64) (T : Type) :
  Core_models.Marker.StructuralPartialEq (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 :
    Core_models.Cmp.PartialEq.AssociatedTypes
    T
    T]
  [trait_constr_Impl_4_i0 : Core_models.Cmp.PartialEq T T ] :
  Core_models.Cmp.PartialEq.AssociatedTypes (FunArray (N) T) (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4
  (N : u64)
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 :
    Core_models.Cmp.PartialEq.AssociatedTypes
    T
    T]
  [trait_constr_Impl_4_i0 : Core_models.Cmp.PartialEq T T ] :
  Core_models.Cmp.PartialEq (FunArray (N) T) (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes
  (N : u64)
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : Core_models.Cmp.Eq.AssociatedTypes
    T]
  [trait_constr_Impl_2_i0 : Core_models.Cmp.Eq T ] :
  Core_models.Cmp.Eq.AssociatedTypes (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2
  (N : u64)
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : Core_models.Cmp.Eq.AssociatedTypes
    T]
  [trait_constr_Impl_2_i0 : Core_models.Cmp.Eq T ] :
  Core_models.Cmp.Eq (FunArray (N) T) :=
  by constructor <;> exact Inhabited.default

@[reducible] instance Impl_11.AssociatedTypes (N : u64) (T : Type) :
  Core_models.Ops.Index.Index.AssociatedTypes (FunArray (N) T) u64
  where
  Output := T

instance Impl_11 (N : u64) (T : Type) :
  Core_models.Ops.Index.Index (FunArray (N) T) u64
  where
  index := fun (self : (FunArray (N) T)) (index : u64) => do
    (Impl_5.get (N) T self index)

end Core_models.Abstractions.Funarr


namespace Core_models.Abstractions.Bitvec

def Impl_10.chunked_shift.chunked_shift (N : u64) (CHUNK : u64) (SHIFTS : u64)
    (bitvec : (BitVec (N)))
    (shl : (Core_models.Abstractions.Funarr.FunArray (SHIFTS) i128)) :
    RustM (BitVec (N)) := do
  (Impl_9.from_fn (N) (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      let nth_bit : u64 ← (i %? CHUNK);
      let nth_chunk : u64 ← (i /? CHUNK);
      let _ ←
        (Hax_lib.assert_prop
          (← (Hax_lib.Prop.Constructors.from_bool
            (← (Rust_primitives.Hax.Int.le
              (← (Rust_primitives.Hax.Int.from_machine nth_chunk))
              (← (Rust_primitives.Hax.Int.sub
                (← (Rust_primitives.Hax.Int.from_machine SHIFTS))
                (← (Hax_lib.Int.Impl_7._unsafe_from_str "1")))))))));
      let _ := Rust_primitives.Hax.Tuple0.mk;
      let _ ←
        (Hax_lib.assert_prop
          (← (Hax_lib.Prop.Constructors.from_bool
            (← (Rust_primitives.Hax.Int.le
              (← (Rust_primitives.Hax.Int.mul
                (← (Rust_primitives.Hax.Int.from_machine nth_chunk))
                (← (Rust_primitives.Hax.Int.from_machine CHUNK))))
              (← (Rust_primitives.Hax.Int.mul
                (← (Rust_primitives.Hax.Int.sub
                  (← (Rust_primitives.Hax.Int.from_machine SHIFTS))
                  (← (Hax_lib.Int.Impl_7._unsafe_from_str "1"))))
                (← (Rust_primitives.Hax.Int.from_machine CHUNK)))))))));
      let _ := Rust_primitives.Hax.Tuple0.mk;
      let shift : i128 ←
        if (← (Rust_primitives.Hax.Machine_int.lt nth_chunk SHIFTS)) then
          shl[nth_chunk]_?
        else
          (pure (0 : i128));
      let local_index : i128 ←
        (Core_models.Num.Impl_4.wrapping_sub
          (← (Rust_primitives.Hax.cast_op nth_bit))
          shift);
      if
      (← ((← (Rust_primitives.Hax.Machine_int.lt
          local_index
          (← (Rust_primitives.Hax.cast_op CHUNK))))
        &&? (← (Rust_primitives.Hax.Machine_int.ge local_index (0 : i128)))))
      then
        let local_index : u64 ← (Rust_primitives.Hax.cast_op local_index);
        let _ ←
          (Hax_lib.assert_prop
            (← (Hax_lib.Prop.Constructors.from_bool
              (← (Rust_primitives.Hax.Int.lt
                (← (Rust_primitives.Hax.Int.add
                  (← (Rust_primitives.Hax.Int.mul
                    (← (Rust_primitives.Hax.Int.from_machine nth_chunk))
                    (← (Rust_primitives.Hax.Int.from_machine CHUNK))))
                  (← (Rust_primitives.Hax.Int.from_machine local_index))))
                (← (Rust_primitives.Hax.Int.mul
                  (← (Rust_primitives.Hax.Int.from_machine SHIFTS))
                  (← (Rust_primitives.Hax.Int.from_machine CHUNK)))))))));
        let _ := Rust_primitives.Hax.Tuple0.mk;
        bitvec[(← ((← (nth_chunk *? CHUNK)) +? local_index))]_?
      else
        (pure Core_models.Abstractions.Bit.Bit.Zero) :
      RustM Core_models.Abstractions.Bit.Bit)))


def Impl_10.chunked_shift (N : u64) (CHUNK : u64) (SHIFTS : u64)
    (self : (BitVec (N)))
    (shl : (Core_models.Abstractions.Funarr.FunArray (SHIFTS) i128)) :
    RustM (BitVec (N)) := do
  (Impl_10.chunked_shift.chunked_shift (N) (CHUNK) (SHIFTS) self shl)


end Core_models.Abstractions.Bitvec


namespace Core_models.Abstractions.Funarr

def Impl_6.pointwise
    (T : Type)
    [trait_constr_pointwise_associated_type_i0 :
      Core_models.Marker.Copy.AssociatedTypes
      T]
    [trait_constr_pointwise_i0 : Core_models.Marker.Copy T ]
    (self : (FunArray ((4 : u64)) T)) :
    RustM (FunArray ((4 : u64)) T) := do
  (Impl_5.from_fn ((4 : u64)) T (u64 -> RustM T)
    (fun i =>
      (do
      match i with
        | 0 => self[(0 : u64)]_?
        | 1 => self[(1 : u64)]_?
        | 2 => self[(2 : u64)]_?
        | 3 => self[(3 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM T)))

def Impl_7.pointwise
    (T : Type)
    [trait_constr_pointwise_associated_type_i0 :
      Core_models.Marker.Copy.AssociatedTypes
      T]
    [trait_constr_pointwise_i0 : Core_models.Marker.Copy T ]
    (self : (FunArray ((8 : u64)) T)) :
    RustM (FunArray ((8 : u64)) T) := do
  (Impl_5.from_fn ((8 : u64)) T (u64 -> RustM T)
    (fun i =>
      (do
      match i with
        | 0 => self[(0 : u64)]_?
        | 1 => self[(1 : u64)]_?
        | 2 => self[(2 : u64)]_?
        | 3 => self[(3 : u64)]_?
        | 4 => self[(4 : u64)]_?
        | 5 => self[(5 : u64)]_?
        | 6 => self[(6 : u64)]_?
        | 7 => self[(7 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM T)))

def Impl_8.pointwise
    (T : Type)
    [trait_constr_pointwise_associated_type_i0 :
      Core_models.Marker.Copy.AssociatedTypes
      T]
    [trait_constr_pointwise_i0 : Core_models.Marker.Copy T ]
    (self : (FunArray ((16 : u64)) T)) :
    RustM (FunArray ((16 : u64)) T) := do
  (Impl_5.from_fn ((16 : u64)) T (u64 -> RustM T)
    (fun i =>
      (do
      match i with
        | 0 => self[(0 : u64)]_?
        | 1 => self[(1 : u64)]_?
        | 2 => self[(2 : u64)]_?
        | 3 => self[(3 : u64)]_?
        | 4 => self[(4 : u64)]_?
        | 5 => self[(5 : u64)]_?
        | 6 => self[(6 : u64)]_?
        | 7 => self[(7 : u64)]_?
        | 8 => self[(8 : u64)]_?
        | 9 => self[(9 : u64)]_?
        | 10 => self[(10 : u64)]_?
        | 11 => self[(11 : u64)]_?
        | 12 => self[(12 : u64)]_?
        | 13 => self[(13 : u64)]_?
        | 14 => self[(14 : u64)]_?
        | 15 => self[(15 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM T)))

end Core_models.Abstractions.Funarr


namespace Core_models.Core_arch.X86.Interpretations.Int_vec

def _mm256_set1_epi32 (x : i32) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32) (fun _ => (do (pure x) : RustM i32)))

def i32_extended64_mul (x : i32) (y : i32) : RustM i64 := do
  ((← (Rust_primitives.Hax.cast_op x : RustM i64)) *? (← (Rust_primitives.Hax.cast_op y : RustM i64)))

def _mm256_mul_epi32
    (x : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (y : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      (i32_extended64_mul
        (← x[(← (i *? (2 : u64)))]_?)
        (← y[(← (i *? (2 : u64)))]_?)) :
      RustM i64)))

def _mm256_sub_epi32
    (x : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (y : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      (Core_models.Num.Impl_2.wrapping_sub (← x[i]_?) (← y[i]_?)) : RustM i32)))

def _mm256_shuffle_epi32 (CONTROL : i32)
    (x : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  let indexes : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u64) ←
    (Core_models.Abstractions.Funarr.Impl_5.from_fn
      ((4 : u64))
      u64
      (u64 -> RustM u64)
      (fun i =>
        (do
        (Rust_primitives.Hax.cast_op
          (← ((← (CONTROL >>>? (← (i *? (2 : u64))))) %? (4 : i32)))) :
        RustM u64)));
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.lt i (4 : u64))) then
        x[(← indexes[i]_?)]_?
      else
        x[(← ((4 : u64) +? (← indexes[(← (i -? (4 : u64)))]_?)))]_? :
      RustM i32)))

def _mm256_blend_epi32 (CONTROL : i32)
    (x : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (y : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← ((← (CONTROL >>>? i)) %? (2 : i32)))
        (0 : i32))) then
        x[i]_?
      else
        y[i]_? :
      RustM i32)))

def _mm256_setzero_si256 (_ : Rust_primitives.Hax.Tuple0) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (Core_models.Abstractions.Bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun _ =>
      (do
      (pure Core_models.Abstractions.Bit.Bit.Zero) :
      RustM Core_models.Abstractions.Bit.Bit)))

def _mm256_set_m128i
    (hi : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (lo : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (Core_models.Abstractions.Bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.lt i (128 : u64))) then
        lo[i]_?
      else
        hi[(← (i -? (128 : u64)))]_? :
      RustM Core_models.Abstractions.Bit.Bit)))

def _mm256_set1_epi16 (a : i16) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16) (fun _ => (do (pure a) : RustM i16)))

def _mm_set1_epi16 (a : i16) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16) (fun _ => (do (pure a) : RustM i16)))

def _mm_set_epi32 (e3 : i32) (e2 : i32) (e1 : i32) (e0 : i32) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      match i with
        | 0 => (pure e0)
        | 1 => (pure e1)
        | 2 => (pure e2)
        | 3 => (pure e3)
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i32)))

def _mm_add_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (Core_models.Num.Impl_1.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i16)))

def _mm256_add_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (Core_models.Num.Impl_1.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i16)))

def _mm256_add_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      (Core_models.Num.Impl_2.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i32)))

def _mm256_add_epi64
    (a : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64))
    (b : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      (Core_models.Num.Impl_3.wrapping_add (← a[i]_?) (← b[i]_?)) : RustM i64)))

def _mm256_abs_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← a[i]_?)
        Core_models.Num.Impl_2.MIN)) then
        a[i]_?
      else
        (Core_models.Num.Impl_2.abs (← a[i]_?)) :
      RustM i32)))

def _mm256_sub_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (Core_models.Num.Impl_1.wrapping_sub (← a[i]_?) (← b[i]_?)) : RustM i16)))

def _mm_sub_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (Core_models.Num.Impl_1.wrapping_sub (← a[i]_?) (← b[i]_?)) : RustM i16)))

def _mm_mullo_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (pure (Rust_primitives.Hax.Tuple2._0
        (← (Core_models.Num.Impl_1.overflowing_mul (← a[i]_?) (← b[i]_?))))) :
      RustM i16)))

def _mm256_cmpgt_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.gt (← a[i]_?) (← b[i]_?))) then
        (pure (-1 : i16))
      else
        (pure (0 : i16)) :
      RustM i16)))

def _mm256_cmpgt_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.gt (← a[i]_?) (← b[i]_?))) then
        (pure (-1 : i32))
      else
        (pure (0 : i32)) :
      RustM i32)))

def _mm256_cmpeq_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.eq (← a[i]_?) (← b[i]_?))) then
        (pure (-1 : i32))
      else
        (pure (0 : i32)) :
      RustM i32)))

def _mm256_sign_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.lt (← b[i]_?) (0 : i32))) then
        if
        (← (Rust_primitives.Hax.Machine_int.eq
          (← a[i]_?)
          Core_models.Num.Impl_2.MIN)) then
          a[i]_?
        else
          (-? (← a[i]_?))
      else
        if (← (Rust_primitives.Hax.Machine_int.gt (← b[i]_?) (0 : i32))) then
          a[i]_?
        else
          (pure (0 : i32)) :
      RustM i32)))

def _mm256_castsi256_ps
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (pure a)

def _mm256_castps_si256
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (pure a)

def _mm256_movemask_ps
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM i32 := do
  let a0 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(0 : u64)]_?) (0 : i32))) then
      (pure (1 : i32))
    else
      (pure (0 : i32));
  let a1 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(1 : u64)]_?) (0 : i32))) then
      (pure (2 : i32))
    else
      (pure (0 : i32));
  let a2 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(2 : u64)]_?) (0 : i32))) then
      (pure (4 : i32))
    else
      (pure (0 : i32));
  let a3 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(3 : u64)]_?) (0 : i32))) then
      (pure (8 : i32))
    else
      (pure (0 : i32));
  let a4 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(4 : u64)]_?) (0 : i32))) then
      (pure (16 : i32))
    else
      (pure (0 : i32));
  let a5 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(5 : u64)]_?) (0 : i32))) then
      (pure (32 : i32))
    else
      (pure (0 : i32));
  let a6 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(6 : u64)]_?) (0 : i32))) then
      (pure (64 : i32))
    else
      (pure (0 : i32));
  let a7 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(7 : u64)]_?) (0 : i32))) then
      (pure (128 : i32))
    else
      (pure (0 : i32));
  ((← ((← ((← ((← ((← ((← (a0 +? a1)) +? a2)) +? a3)) +? a4)) +? a5)) +? a6))
    +? a7)

def _mm_mulhi_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (Rust_primitives.Hax.cast_op
        (← ((← ((← (Rust_primitives.Hax.cast_op (β := i32) (← a[i]_?)))
            *? (← (Rust_primitives.Hax.cast_op (β := i32) (← b[i]_?)))))
          >>>? (16 : i32)))) :
      RustM i16)))

def _mm256_mullo_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      (pure (Rust_primitives.Hax.Tuple2._0
        (← (Core_models.Num.Impl_2.overflowing_mul (← a[i]_?) (← b[i]_?))))) :
      RustM i32)))

def _mm256_mulhi_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      (Rust_primitives.Hax.cast_op
        (← ((← ((← (Rust_primitives.Hax.cast_op (β := i32) (← a[i]_?)))
            *? (← (Rust_primitives.Hax.cast_op (β := i32) (← b[i]_?)))))
          >>>? (16 : i32)))) :
      RustM i16)))

def _mm256_mul_epu32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) u32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    u64
    (u64 -> RustM u64)
    (fun i =>
      (do
      ((← (Rust_primitives.Hax.cast_op (β := u64) (← a[(← (i *? (2 : u64)))]_?)))
        *? (← (Rust_primitives.Hax.cast_op (β := u64) (← b[(← (i *? (2 : u64)))]_?)))) :
      RustM u64)))

def _mm256_and_si256
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (Core_models.Abstractions.Bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      match (Rust_primitives.Hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(Core_models.Abstractions.Bit.Bit.One ),
           (Core_models.Abstractions.Bit.Bit.One )⟩ =>
          (pure Core_models.Abstractions.Bit.Bit.One)
        | _ => (pure Core_models.Abstractions.Bit.Bit.Zero) :
      RustM Core_models.Abstractions.Bit.Bit)))

def _mm256_or_si256
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (Core_models.Abstractions.Bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      match (Rust_primitives.Hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(Core_models.Abstractions.Bit.Bit.Zero ),
           (Core_models.Abstractions.Bit.Bit.Zero )⟩ =>
          (pure Core_models.Abstractions.Bit.Bit.Zero)
        | _ => (pure Core_models.Abstractions.Bit.Bit.One) :
      RustM Core_models.Abstractions.Bit.Bit)))

def _mm256_testz_si256
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM i32 := do
  let c : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) ←
    (Core_models.Abstractions.Bitvec.Impl_9.from_fn
      ((256 : u64))
      (u64 -> RustM Core_models.Abstractions.Bit.Bit)
      (fun i =>
        (do
        match (Rust_primitives.Hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
          | ⟨(Core_models.Abstractions.Bit.Bit.One ),
             (Core_models.Abstractions.Bit.Bit.One )⟩ =>
            (pure Core_models.Abstractions.Bit.Bit.One)
          | _ => (pure Core_models.Abstractions.Bit.Bit.Zero) :
        RustM Core_models.Abstractions.Bit.Bit)));
  let all_zero : Bool ←
    (Core_models.Abstractions.Bitvec.Impl_10.fold ((256 : u64)) Bool
      c
      true
      (fun acc bit =>
        (do
        (acc
          &&? (← (Core_models.Cmp.PartialEq.eq
            Core_models.Abstractions.Bit.Bit
            Core_models.Abstractions.Bit.Bit
            bit
            Core_models.Abstractions.Bit.Bit.Zero))) :
        RustM Bool)));
  if all_zero then (pure (1 : i32)) else (pure (0 : i32))

def _mm256_xor_si256
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (Core_models.Abstractions.Bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      match (Rust_primitives.Hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(Core_models.Abstractions.Bit.Bit.Zero ),
           (Core_models.Abstractions.Bit.Bit.Zero )⟩ =>
          (pure Core_models.Abstractions.Bit.Bit.Zero)
        | ⟨(Core_models.Abstractions.Bit.Bit.One ),
           (Core_models.Abstractions.Bit.Bit.One )⟩ =>
          (pure Core_models.Abstractions.Bit.Bit.Zero)
        | _ => (pure Core_models.Abstractions.Bit.Bit.One) :
      RustM Core_models.Abstractions.Bit.Bit)))

def _mm256_srai_epi16 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      let imm8 : i32 ← (Core_models.Num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (Rust_primitives.Hax.Machine_int.gt imm8 (15 : i32))) then
        if (← (Rust_primitives.Hax.Machine_int.lt (← a[i]_?) (0 : i16))) then
          (pure (-1 : i16))
        else
          (pure (0 : i16))
      else
        ((← a[i]_?) >>>? imm8) :
      RustM i16)))

def _mm256_srai_epi32 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let imm8 : i32 ← (Core_models.Num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (Rust_primitives.Hax.Machine_int.gt imm8 (31 : i32))) then
        if (← (Rust_primitives.Hax.Machine_int.lt (← a[i]_?) (0 : i32))) then
          (pure (-1 : i32))
        else
          (pure (0 : i32))
      else
        ((← a[i]_?) >>>? imm8) :
      RustM i32)))

def _mm256_srli_epi16 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      let imm8 : i32 ← (Core_models.Num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (Rust_primitives.Hax.Machine_int.gt imm8 (15 : i32))) then
        (pure (0 : i16))
      else
        (Rust_primitives.Hax.cast_op
          (← ((← (Rust_primitives.Hax.cast_op (β := u16) (← a[i]_?))) >>>? imm8))) :
      RustM i16)))

def _mm256_srli_epi32 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let imm8 : i32 ← (Core_models.Num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (Rust_primitives.Hax.Machine_int.gt imm8 (31 : i32))) then
        (pure (0 : i32))
      else
        (Rust_primitives.Hax.cast_op
          (← ((← (Rust_primitives.Hax.cast_op (β := u32) (← a[i]_?))) >>>? imm8))) :
      RustM i32)))

def _mm_srli_epi64 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((2 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      let imm8 : i32 ← (Core_models.Num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (Rust_primitives.Hax.Machine_int.gt imm8 (63 : i32))) then
        (pure (0 : i64))
      else
        (Rust_primitives.Hax.cast_op
          (← ((← (Rust_primitives.Hax.cast_op (β := u64) (← a[i]_?))) >>>? imm8))) :
      RustM i64)))

def _mm256_slli_epi32 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      let imm8 : i32 ← (Core_models.Num.Impl_2.rem_euclid IMM8 (256 : i32));
      if (← (Rust_primitives.Hax.Machine_int.gt imm8 (31 : i32))) then
        (pure (0 : i32))
      else
        (Rust_primitives.Hax.cast_op
          (← ((← (Rust_primitives.Hax.cast_op (β := u32) (← a[i]_?))) <<<? imm8))) :
      RustM i32)))

def _mm256_permute4x64_epi64 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  let indexes : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) u64) ←
    (Core_models.Abstractions.Funarr.Impl_5.from_fn
      ((4 : u64))
      u64
      (u64 -> RustM u64)
      (fun i =>
        (do
        (Rust_primitives.Hax.cast_op
          (← ((← (IMM8 >>>? (← (i *? (2 : u64))))) %? (4 : i32)))) :
        RustM u64)));
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64) (fun i => (do a[(← indexes[i]_?)]_? : RustM i64)))

def _mm256_unpackhi_epi64
    (a : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64))
    (b : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      match i with
        | 0 => a[(1 : u64)]_?
        | 1 => b[(1 : u64)]_?
        | 2 => a[(3 : u64)]_?
        | 3 => b[(3 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i64)))

def _mm256_unpacklo_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      match i with
        | 0 => a[(0 : u64)]_?
        | 1 => b[(0 : u64)]_?
        | 2 => a[(1 : u64)]_?
        | 3 => b[(1 : u64)]_?
        | 4 => a[(4 : u64)]_?
        | 5 => b[(4 : u64)]_?
        | 6 => a[(5 : u64)]_?
        | 7 => b[(5 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i32)))

def _mm256_unpackhi_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      match i with
        | 0 => a[(2 : u64)]_?
        | 1 => b[(2 : u64)]_?
        | 2 => a[(3 : u64)]_?
        | 3 => b[(3 : u64)]_?
        | 4 => a[(6 : u64)]_?
        | 5 => b[(6 : u64)]_?
        | 6 => a[(7 : u64)]_?
        | 7 => b[(7 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i32)))

def _mm256_castsi128_si256
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (Core_models.Abstractions.Bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.lt i (128 : u64))) then
        a[i]_?
      else
        (pure Core_models.Abstractions.Bit.Bit.Zero) :
      RustM Core_models.Abstractions.Bit.Bit)))

def _mm256_cvtepi16_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i => (do (Rust_primitives.Hax.cast_op (← a[i]_?)) : RustM i32)))

def _mm_packs_epi16
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i8) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i8
    (u64 -> RustM i8)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.lt i (8 : u64))) then
        if
        (← (Rust_primitives.Hax.Machine_int.gt
          (← a[i]_?)
          (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl.MAX)))) then
          (pure Core_models.Num.Impl.MAX)
        else
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← a[i]_?)
            (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl.MIN)))) then
            (pure Core_models.Num.Impl.MIN)
          else
            (Rust_primitives.Hax.cast_op (← a[i]_?))
      else
        if
        (← (Rust_primitives.Hax.Machine_int.gt
          (← b[(← (i -? (8 : u64)))]_?)
          (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl.MAX)))) then
          (pure Core_models.Num.Impl.MAX)
        else
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← b[(← (i -? (8 : u64)))]_?)
            (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl.MIN)))) then
            (pure Core_models.Num.Impl.MIN)
          else
            (Rust_primitives.Hax.cast_op (← b[(← (i -? (8 : u64)))]_?)) :
      RustM i8)))

def _mm256_packs_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.lt i (4 : u64))) then
        if
        (← (Rust_primitives.Hax.Machine_int.gt
          (← a[i]_?)
          (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MAX)))) then
          (pure Core_models.Num.Impl_1.MAX)
        else
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← a[i]_?)
            (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MIN)))) then
            (pure Core_models.Num.Impl_1.MIN)
          else
            (Rust_primitives.Hax.cast_op (← a[i]_?))
      else
        if (← (Rust_primitives.Hax.Machine_int.lt i (8 : u64))) then
          if
          (← (Rust_primitives.Hax.Machine_int.gt
            (← b[(← (i -? (4 : u64)))]_?)
            (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MAX)))) then
            (pure Core_models.Num.Impl_1.MAX)
          else
            if
            (← (Rust_primitives.Hax.Machine_int.lt
              (← b[(← (i -? (4 : u64)))]_?)
              (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MIN))))
            then
              (pure Core_models.Num.Impl_1.MIN)
            else
              (Rust_primitives.Hax.cast_op (← b[(← (i -? (4 : u64)))]_?))
        else
          if (← (Rust_primitives.Hax.Machine_int.lt i (12 : u64))) then
            if
            (← (Rust_primitives.Hax.Machine_int.gt
              (← a[(← (i -? (4 : u64)))]_?)
              (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MAX))))
            then
              (pure Core_models.Num.Impl_1.MAX)
            else
              if
              (← (Rust_primitives.Hax.Machine_int.lt
                (← a[(← (i -? (4 : u64)))]_?)
                (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MIN))))
              then
                (pure Core_models.Num.Impl_1.MIN)
              else
                (Rust_primitives.Hax.cast_op (← a[(← (i -? (4 : u64)))]_?))
          else
            if
            (← (Rust_primitives.Hax.Machine_int.gt
              (← b[(← (i -? (8 : u64)))]_?)
              (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MAX))))
            then
              (pure Core_models.Num.Impl_1.MAX)
            else
              if
              (← (Rust_primitives.Hax.Machine_int.lt
                (← b[(← (i -? (8 : u64)))]_?)
                (← (Rust_primitives.Hax.cast_op Core_models.Num.Impl_1.MIN))))
              then
                (pure Core_models.Num.Impl_1.MIN)
              else
                (Rust_primitives.Hax.cast_op (← b[(← (i -? (8 : u64)))]_?)) :
      RustM i16)))

def _mm256_inserti128_si256 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128))
    (b : (Core_models.Abstractions.Funarr.FunArray ((1 : u64)) i128)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((2 : u64))
    i128
    (u64 -> RustM i128)
    (fun i =>
      (do
      if
      (← (Rust_primitives.Hax.Machine_int.eq (← (IMM8 %? (2 : i32))) (0 : i32)))
      then
        match i with
          | 0 => b[(0 : u64)]_?
          | 1 => a[(1 : u64)]_?
          | _ =>
            (Rust_primitives.Hax.never_to_any
              (← (Core_models.Panicking.panic
                "internal error: entered unreachable code")))
      else
        match i with
          | 0 => a[(0 : u64)]_?
          | 1 => b[(0 : u64)]_?
          | _ =>
            (Rust_primitives.Hax.never_to_any
              (← (Core_models.Panicking.panic
                "internal error: entered unreachable code"))) :
      RustM i128)))

def _mm256_blend_epi16 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16))
    (b : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i16) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((16 : u64))
    i16
    (u64 -> RustM i16)
    (fun i =>
      (do
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← ((← (IMM8 >>>? (← (i %? (8 : u64))))) %? (2 : i32)))
        (0 : i32))) then
        a[i]_?
      else
        b[i]_? :
      RustM i16)))

def _mm256_blendv_ps
    (a : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32))
    (mask : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((8 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if (← (Rust_primitives.Hax.Machine_int.lt (← mask[i]_?) (0 : i32))) then
        b[i]_?
      else
        a[i]_? :
      RustM i32)))

def _mm_movemask_epi8
    (a : (Core_models.Abstractions.Funarr.FunArray ((16 : u64)) i8)) :
    RustM i32 := do
  let a0 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(0 : u64)]_?) (0 : i8))) then
      (pure (1 : i32))
    else
      (pure (0 : i32));
  let a1 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(1 : u64)]_?) (0 : i8))) then
      (pure (2 : i32))
    else
      (pure (0 : i32));
  let a2 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(2 : u64)]_?) (0 : i8))) then
      (pure (4 : i32))
    else
      (pure (0 : i32));
  let a3 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(3 : u64)]_?) (0 : i8))) then
      (pure (8 : i32))
    else
      (pure (0 : i32));
  let a4 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(4 : u64)]_?) (0 : i8))) then
      (pure (16 : i32))
    else
      (pure (0 : i32));
  let a5 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(5 : u64)]_?) (0 : i8))) then
      (pure (32 : i32))
    else
      (pure (0 : i32));
  let a6 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(6 : u64)]_?) (0 : i8))) then
      (pure (64 : i32))
    else
      (pure (0 : i32));
  let a7 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(7 : u64)]_?) (0 : i8))) then
      (pure (128 : i32))
    else
      (pure (0 : i32));
  let a8 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(8 : u64)]_?) (0 : i8))) then
      (pure (256 : i32))
    else
      (pure (0 : i32));
  let a9 : i32 ←
    if (← (Rust_primitives.Hax.Machine_int.lt (← a[(9 : u64)]_?) (0 : i8))) then
      (pure (512 : i32))
    else
      (pure (0 : i32));
  let a10 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(10 : u64)]_?) (0 : i8))) then
      (pure (1024 : i32))
    else
      (pure (0 : i32));
  let a11 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(11 : u64)]_?) (0 : i8))) then
      (pure (2048 : i32))
    else
      (pure (0 : i32));
  let a12 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(12 : u64)]_?) (0 : i8))) then
      (pure (4096 : i32))
    else
      (pure (0 : i32));
  let a13 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(13 : u64)]_?) (0 : i8))) then
      (pure (8192 : i32))
    else
      (pure (0 : i32));
  let a14 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(14 : u64)]_?) (0 : i8))) then
      (pure (16384 : i32))
    else
      (pure (0 : i32));
  let a15 : i32 ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt (← a[(15 : u64)]_?) (0 : i8))) then
      (pure (32768 : i32))
    else
      (pure (0 : i32));
  ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← ((← (a0 +? a1)) +? a2))
                            +? a3))
                          +? a4))
                        +? a5))
                      +? a6))
                    +? a7))
                  +? a8))
                +? a9))
              +? a10))
            +? a11))
          +? a12))
        +? a13))
      +? a14))
    +? a15)

def _mm256_srlv_epi64
    (a : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64))
    (b : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      if
      (← ((← (Rust_primitives.Hax.Machine_int.gt (← b[i]_?) (63 : i64)))
        ||? (← (Rust_primitives.Hax.Machine_int.lt (← b[i]_?) (0 : i64))))) then
        (pure (0 : i64))
      else
        (Rust_primitives.Hax.cast_op
          (← ((← (Rust_primitives.Hax.cast_op (β := u64) (← a[i]_?))) >>>? (← b[i]_?)))) :
      RustM i64)))

def _mm_sllv_epi32
    (a : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i32))
    (b : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i32)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i32) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i32
    (u64 -> RustM i32)
    (fun i =>
      (do
      if
      (← ((← (Rust_primitives.Hax.Machine_int.gt (← b[i]_?) (31 : i32)))
        ||? (← (Rust_primitives.Hax.Machine_int.lt (← b[i]_?) (0 : i32))))) then
        (pure (0 : i32))
      else
        (Rust_primitives.Hax.cast_op
          (← ((← (Rust_primitives.Hax.cast_op (β := u32) (← a[i]_?))) <<<? (← b[i]_?)))) :
      RustM i32)))

def _mm256_slli_epi64 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      let imm8 : i32 ← (IMM8 %? (256 : i32));
      if (← (Rust_primitives.Hax.Machine_int.gt imm8 (63 : i32))) then
        (pure (0 : i64))
      else
        (Rust_primitives.Hax.cast_op
          (← ((← (Rust_primitives.Hax.cast_op (β := u64) (← a[i]_?))) <<<? imm8))) :
      RustM i64)))

def _mm256_bsrli_epi128 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((2 : u64))
    i128
    (u64 -> RustM i128)
    (fun i =>
      (do
      let tmp : i32 ← (IMM8 %? (256 : i32));
      let tmp : i32 ← (tmp %? (16 : i32));
      (Rust_primitives.Hax.cast_op
        (← ((← (Rust_primitives.Hax.cast_op (β := u128) (← a[i]_?)))
          >>>? (← (tmp *? (8 : i32)))))) :
      RustM i128)))

def _mm256_andnot_si256
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) := do
  (Core_models.Abstractions.Bitvec.Impl_9.from_fn
    ((256 : u64))
    (u64 -> RustM Core_models.Abstractions.Bit.Bit)
    (fun i =>
      (do
      match (Rust_primitives.Hax.Tuple2.mk (← a[i]_?) (← b[i]_?)) with
        | ⟨(Core_models.Abstractions.Bit.Bit.Zero ),
           (Core_models.Abstractions.Bit.Bit.One )⟩ =>
          (pure Core_models.Abstractions.Bit.Bit.One)
        | _ => (pure Core_models.Abstractions.Bit.Bit.Zero) :
      RustM Core_models.Abstractions.Bit.Bit)))

def _mm256_set1_epi64x (a : i64) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64) (fun _ => (do (pure a) : RustM i64)))

def _mm256_set_epi64x (e3 : i64) (e2 : i64) (e1 : i64) (e0 : i64) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      match i with
        | 0 => (pure e0)
        | 1 => (pure e1)
        | 2 => (pure e2)
        | 3 => (pure e3)
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i64)))

def _mm256_unpacklo_epi64
    (a : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64))
    (b : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((4 : u64))
    i64
    (u64 -> RustM i64)
    (fun i =>
      (do
      match i with
        | 0 => a[(0 : u64)]_?
        | 1 => b[(0 : u64)]_?
        | 2 => a[(2 : u64)]_?
        | 3 => b[(2 : u64)]_?
        | _ =>
          (Rust_primitives.Hax.never_to_any
            (← (Core_models.Panicking.panic
              "internal error: entered unreachable code"))) :
      RustM i64)))

def _mm256_permute2x128_si256 (IMM8 : i32)
    (a : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128))
    (b : (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128)) :
    RustM (Core_models.Abstractions.Funarr.FunArray ((2 : u64)) i128) := do
  (Core_models.Abstractions.Funarr.Impl_5.from_fn
    ((2 : u64))
    i128
    (u64 -> RustM i128)
    (fun i =>
      (do
      let control : i32 ← (IMM8 >>>? (← (i *? (4 : u64))));
      if
      (← (Rust_primitives.Hax.Machine_int.eq
        (← ((← (control >>>? (3 : i32))) %? (2 : i32)))
        (1 : i32))) then
        (pure (0 : i128))
      else
        match (← (control %? (4 : i32))) with
          | 0 => a[(0 : u64)]_?
          | 1 => a[(1 : u64)]_?
          | 2 => b[(0 : u64)]_?
          | 3 => b[(1 : u64)]_?
          | _ =>
            (Rust_primitives.Hax.never_to_any
              (← (Core_models.Panicking.panic
                "internal error: entered unreachable code"))) :
      RustM i128)))

end Core_models.Core_arch.X86.Interpretations.Int_vec


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

--  An F* attribute that marks an item as being an lifting lemma.
def ETA_MATCH_EXPAND : Rust_primitives.Hax.Tuple0 :=
  RustM.of_isOk (do Rust_primitives.Hax.Tuple0.mk) (by rfl)

opaque pointwise_i32x8
    (x : (Core_models.Abstractions.Funarr.FunArray ((8 : u64)) i32)) :
    RustM Rust_primitives.Hax.Tuple0 

opaque pointwise_i64x4
    (x : (Core_models.Abstractions.Funarr.FunArray ((4 : u64)) i64)) :
    RustM Rust_primitives.Hax.Tuple0 

--  An F* attribute that marks an item as being an lifting lemma.
def LIFT_LEMMA : Rust_primitives.Hax.Tuple0 :=
  RustM.of_isOk (do Rust_primitives.Hax.Tuple0.mk) (by rfl)

def __2 : Rust_primitives.Hax.Tuple0 :=
  RustM.of_isOk (do Rust_primitives.Hax.Tuple0.mk) (by rfl)

--  F* tactic: specialization of `Tactics.Circuits.flatten_circuit`.
def flatten_circuit (_ : Rust_primitives.Hax.Tuple0) :
    RustM Rust_primitives.Hax.Tuple0 := do
  (pure Rust_primitives.Hax.Tuple0.mk)

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_packs_epi16)
opaque _mm_packs_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_packs_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set1_epi16)
opaque _mm_set1_epi16 (_ : i16) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_set1_epi16 (x : i16) : RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_set_epi32)
opaque _mm_set_epi32 (_ : i32) (_ : i32) (_ : i32) (_ : i32) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_set_epi32 (e3 : i32) (e2 : i32) (e1 : i32) (e0 : i32) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_add_epi16)
opaque _mm_add_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_add_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mullo_epi16)
opaque _mm_mullo_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_mullo_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_mulhi_epi16)
opaque _mm_mulhi_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_mulhi_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_srli_epi64)
opaque _mm_srli_epi64 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_srli_epi64 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Sse2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_movemask_epi8)
opaque _mm_movemask_epi8
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM i32 

end Core_models.Core_arch.X86.Sse2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_movemask_epi8
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi64x)
opaque _mm256_set1_epi64x (_ : i64) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_set1_epi64x (a : i64) : RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set_epi64x)
opaque _mm256_set_epi64x (_ : i64) (_ : i64) (_ : i64) (_ : i64) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_set_epi64x (e3 : i64) (e2 : i64) (e1 : i64) (e0 : i64) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blendv_ps)
opaque _mm256_blendv_ps
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_blendv_ps
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (c : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_movemask_ps)
opaque _mm256_movemask_ps
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM i32 

end Core_models.Core_arch.X86.Avx


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_movemask_ps
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx

--  This is opaque to Hax: it is defined only via the integer
--  interpretation. See `interpretations::int_vec::_mm256_set1_epi32`.
opaque _mm256_set1_epi32 (_ : i32) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_set1_epi32 (x : i32) : RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_set1_epi16)
opaque _mm256_set1_epi16 (_ : i16) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_set1_epi16 (x : i16) : RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi32)
opaque _mm256_blend_epi32 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_blend_epi32 (CONTROL : i32)
    (x : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (y : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_shuffle_epi32)
opaque _mm256_shuffle_epi32 (MASK : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_shuffle_epi32 (CONTROL : i32)
    (x : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi32)
opaque _mm256_sub_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_sub_epi32
    (x : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (y : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epi32)
opaque _mm256_mul_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_mul_epi32
    (x : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (y : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi16)
opaque _mm256_add_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_add_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi32)
opaque _mm256_add_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_add_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_add_epi64)
opaque _mm256_add_epi64
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_add_epi64
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_abs_epi32)
opaque _mm256_abs_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_abs_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sub_epi16)
opaque _mm256_sub_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_sub_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi16)
opaque _mm256_cmpgt_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_cmpgt_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cmpgt_epi32)
opaque _mm256_cmpgt_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_cmpgt_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_sign_epi32)
opaque _mm256_sign_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_sign_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mullo_epi32)
opaque _mm256_mullo_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_mullo_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mulhi_epi16)
opaque _mm256_mulhi_epi16
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_mulhi_epi16
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_mul_epu32)
opaque _mm256_mul_epu32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_mul_epu32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi16)
opaque _mm256_srai_epi16 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_srai_epi16 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srai_epi32)
opaque _mm256_srai_epi32 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_srai_epi32 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi16)
opaque _mm256_srli_epi16 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_srli_epi16 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srli_epi32)
opaque _mm256_srli_epi32 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_srli_epi32 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi32)
opaque _mm256_slli_epi32 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_slli_epi32 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute4x64_epi64)
opaque _mm256_permute4x64_epi64 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_permute4x64_epi64 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi64)
opaque _mm256_unpackhi_epi64
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_unpackhi_epi64
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi32)
opaque _mm256_unpacklo_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_unpacklo_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpackhi_epi32)
opaque _mm256_unpackhi_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_unpackhi_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_cvtepi16_epi32)
opaque _mm256_cvtepi16_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_cvtepi16_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_packs_epi32)
opaque _mm256_packs_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_packs_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_inserti128_si256)
opaque _mm256_inserti128_si256 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_inserti128_si256 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_blend_epi16)
opaque _mm256_blend_epi16 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_blend_epi16 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_srlv_epi64)
opaque _mm256_srlv_epi64
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_srlv_epi64
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm_sllv_epi32)
opaque _mm_sllv_epi32
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm_sllv_epi32
    (a : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((128 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_slli_epi64)
opaque _mm256_slli_epi64 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_slli_epi64 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_bsrli_epi128)
--  NOTE: the bsrli here is different from intel specification. In the intel specification, if an IMM8 is given whose first 8 bits are higher than 15, it fixes it to 16.
--  However, the Rust implementation erroneously takes the input modulo 16. Thus, instead of shifting by 16 bits at an input of 16, it shifts by 0.
--  We are currently modelling the Rust implementation.
opaque _mm256_bsrli_epi128 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_bsrli_epi128 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_unpacklo_epi64)
opaque _mm256_unpacklo_epi64
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_unpacklo_epi64
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas


namespace Core_models.Core_arch.X86.Avx2

--  [Intel Documentation](https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_permute2x128_si256)
opaque _mm256_permute2x128_si256 (IMM8 : i32)
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (_ : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))) 

end Core_models.Core_arch.X86.Avx2


namespace Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

opaque _mm256_permute2x128_si256 (IMM8 : i32)
    (a : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64))))
    (b : (Core_models.Abstractions.Bitvec.BitVec ((256 : u64)))) :
    RustM Rust_primitives.Hax.Tuple0 

end Core_models.Core_arch.X86.Interpretations.Int_vec.Lemmas

