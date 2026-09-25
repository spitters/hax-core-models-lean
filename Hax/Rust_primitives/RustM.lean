import Hax.Tactic.Init
import Hax.MissingLean.Init.While
import Std.Tactic.Do

open Std.Do
open Std.Tactic

/-
# Monadic encoding

The encoding is based on the `RustM` monad: all rust computations are wrapped
in the monad, representing the fact that they are not total.

It borrows some definitions from the Aeneas project
(https://github.com/AeneasVerif/aeneas/)

-/

/--
  (Aeneas) Error cases
-/
inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq, DecidableEq
open Error

/--
  RustM monad (corresponding to Aeneas's `Result` monad), representing
  possible results of rust computations
-/
inductive RustM.{u} (α : Type u) where
  | ok (v: α): RustM α
  | fail (e: Error): RustM α
  | div
deriving Repr, BEq, DecidableEq, Inhabited

namespace RustM

@[simp, hax_bv_decide]
instance instPure: Pure RustM where
  pure x := .ok x

@[simp]
def bind {α β : Type} (x: RustM α) (f: α -> RustM β) := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

@[simp]
def ofOption {α} (x:Option α) (e: Error) : RustM α := match x with
  | .some v => pure v
  | .none => .fail e

@[reducible]
def isOk {α : Type} (x: RustM α) : Bool := match x with
| .ok _ => true
| _ => false

@[reducible, hax_bv_decide]
def of_isOk {α : Type} (x: RustM α) (h: RustM.isOk x): α :=
  match x with
  | .ok v => v

@[simp, spec]
def ok_of_isOk {α : Type} (v : α) (h: isOk (ok v)): (ok v).of_isOk h = v := by rfl

@[simp, hax_bv_decide]
instance instMonad : Monad RustM where
  pure := pure
  bind := RustM.bind

@[simp, grind =] theorem pure_eq {α : Type} (x : α) : (pure x : RustM α) = .ok x := rfl

@[simp, grind =] theorem bind_eq {α β : Type} (x : RustM α) (f : α → RustM β) :
    (x >>= f) = RustM.bind x f := rfl

instance instLawfulMonad : LawfulMonad RustM := LawfulMonad.mk'
  (id_map := by intro α x; cases x <;> rfl)
  (pure_bind := by intros; rfl)
  (bind_assoc := by intro α β γ x f g; cases x <;> rfl)

@[simp]
instance instWP : WP RustM (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (Pure.pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

@[simp]
instance instWPMonad : WPMonad RustM (.except Error .pure) where
  wp_pure a := WPMonad.wp_pure (m := Except Error) a
  wp_bind x f := by
    ext Q
    cases x <;> first
      | rfl
      | simp [bind_eq, RustM.bind, wp, PredTrans.bind, PredTrans.const, Bind.bind]
      | simp [bind_eq, RustM.bind, WP.pure, WP.throw, PredTrans.bind, PredTrans.const, Bind.bind]

@[simp, grind =] theorem wp_ok {α : Type} (v : α) (Q : PostCond α (.except Error .pure)) :
    (wp (RustM.ok v)).apply Q = Q.1 v := rfl

@[simp, grind =] theorem wp_fail {α : Type} (e : Error) (Q : PostCond α (.except Error .pure)) :
    (wp (RustM.fail e : RustM α)).apply Q = Q.2.1 e := rfl

@[simp, grind =] theorem wp_div {α : Type} (Q : PostCond α (.except Error .pure)) :
    (wp (RustM.div : RustM α)).apply Q = ⌜False⌝ := rfl

@[default_instance]
instance instCoe {α} : Coe α (RustM α) where
  coe x := pure x

@[simp, spec, default_instance]
instance {α} : Coe (RustM (RustM α)) (RustM α) where
  coe x := match x with
  | .ok y => y
  | .fail e => .fail e
  | .div => .div

section Order

open Lean.Order

/- These instances are required to use `partial_fixpoint` in the `RustM` monad. -/

instance {α} : PartialOrder (RustM α) := inferInstanceAs (PartialOrder (FlatOrder RustM.div))

noncomputable instance {α} : CCPO (RustM α) := inferInstanceAs (CCPO (FlatOrder RustM.div))

noncomputable instance : MonoBind RustM where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹RustM _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl

open Lean Order in
/-- `Loop.MonoLoopCombinator` is used to implement while loops in `RustM`: -/
instance {β : Type} (f : Unit → β → RustM (ForInStep β)) : Loop.MonoLoopCombinator f := {
  mono := by
    unfold Loop.loopCombinator
    repeat monotonicity
}

end Order

end RustM
