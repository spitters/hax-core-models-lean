import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Tuple
import Hax.Rust_primitives.Num

open Rust_primitives.Hax

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

abbrev RustSlice := Array
abbrev RustVector := Array

def Alloc.Alloc.Global : Type := Unit

abbrev Alloc.Vec.Vec (α: Type) (_Allocator:Type) : Type := Array α

def Alloc.Vec.Impl.new (α: Type) (_:Tuple0) : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure ((List.nil).toArray)

def Alloc.Vec.Impl_1.len (α: Type) (_Allocator: Type) (x: Alloc.Vec.Vec α Alloc.Alloc.Global) : RustM usize :=
  pure x.size

def Alloc.Vec.Impl_2.extend_from_slice α (_Allocator: Type) (x: Alloc.Vec.Vec α Alloc.Alloc.Global) (y: Array α)
  : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global):=
  pure (x.append y)

def Alloc.Slice.Impl.to_vec α (a:  Array α) : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure a

-- Construct an empty `Vec` with the given capacity hint. The capacity
-- is informational only in Rust; semantically the value is the empty
-- vector. Matches the signature emitted by hax for
-- `Vec::with_capacity(n)`.
def Alloc.Vec.Impl.with_capacity (α: Type) (_cap: usize)
    : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure (List.nil).toArray

-- `Vec::push(self, x)` — append at the tail. Returns the updated Vec.
def Alloc.Vec.Impl_1.push (α: Type) (_Allocator: Type)
    (x: Alloc.Vec.Vec α Alloc.Alloc.Global) (v: α)
    : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure (x.push v)

-- `Vec::is_empty(self)` — true iff size is 0.
def Alloc.Vec.Impl_1.is_empty (α: Type) (_Allocator: Type)
    (x: Alloc.Vec.Vec α Alloc.Alloc.Global) : RustM Bool :=
  pure (x.size = 0)

-- `vec![val; n]` — repeat `val` n times.
def Alloc.Vec.from_elem (α: Type) (val: α) (n: usize)
    : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure (Array.replicate n.toNat val)

-- `Vec::as_slice(&self)`. Our representation makes Vec and Slice the
-- same Array, so this is the identity.
def Alloc.Vec.Impl_1.as_slice (α: Type) (_Allocator: Type)
    (x: Alloc.Vec.Vec α Alloc.Alloc.Global) : RustM (RustSlice α) :=
  pure x

-- For
instance {α n} : Coe (Array α) (RustM (Vector α n)) where
  coe x :=
    if h: x.size = n then by
      rw [←h]
      apply pure
      apply (Array.toVector x)
    else .fail (.arrayOutOfBounds)

end RustVectors
