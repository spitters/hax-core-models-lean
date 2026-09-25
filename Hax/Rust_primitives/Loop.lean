import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num
import Hax.MissingLean.Std.Do.Triple.SpecLemmas

open Std.Do

/-

# Loops

-/
open Lean

/-- `while_loop` is used to represent while-loops in `RustM` programs. The function provides
  extra arguments to store a termination measure and an invariant, which can be used to verify the
  program. The arguments `pureInv` and `pureTermination` are usually not provided explicitly and
  derived by the default tactic given below. -/
noncomputable def Rust_primitives.Hax.while_loop {β : Type}
    (inv: β → RustM Prop)
    (cond: β → RustM Bool)
    (termination : β -> RustM Hax_lib.Int.Int)
    (init : β)
    (body : β -> RustM β)
    (pureInv:
        {i : β -> Prop // ∀ b, ⦃⌜ True ⌝⦄ inv b ⦃⇓ r => ⌜ r = (i b) ⌝⦄} := by
      constructor; intro; mvcgen)
    (_pureTermination :
        {t : β -> Nat // ∀ b, ⦃⌜ True ⌝⦄ termination b ⦃⇓ r => ⌜ r = Int.ofNat (t b) ⌝⦄} := by
      constructor; intro; mvcgen)
    (pureCond :
        {c : β -> Bool // ∀ b, ⦃⌜ pureInv.val b ⌝⦄ cond b ⦃⇓ r => ⌜ r = c b ⌝⦄} := by
      constructor; intro; mvcgen) : RustM β :=
  Loop.MonoLoopCombinator.while_loop Loop.mk pureCond.val init body

/-- Local mirror of `Core_models.Ops.Control_flow.ControlFlow`, defined
    here to avoid an import cycle (`Core_models.Extracted` imports
    `MissingCore` which imports `Rust_primitives`). The user-facing
    `Hax/WhileLoopReturn.lean` adds an `abbrev` so the two types are
    interchangeable for hax-emitted callers. -/
inductive Rust_primitives.Hax.LoopReturn (B : Type) (C : Type) : Type
| Continue : C -> Rust_primitives.Hax.LoopReturn B C
| Break : B -> Rust_primitives.Hax.LoopReturn B C

/-- See `Hax/WhileLoopReturn.lean` for the user-facing version that
    pattern-matches against the `Core_models.Ops.Control_flow.ControlFlow`
    constructors used by hax-emitted code. -/
def Rust_primitives.Hax.while_loop_return {β γ : Type}
    (inv: β → RustM Prop)
    (cond: β → RustM Bool)
    (termination : β -> RustM Hax_lib.Int.Int)
    (init : β)
    (body : β -> RustM (Rust_primitives.Hax.LoopReturn γ β))
    (pureInv:
        {i : β -> Prop // ∀ b, ⦃⌜ True ⌝⦄ inv b ⦃⇓ r => ⌜ r = (i b) ⌝⦄} := by
      constructor; intro; mvcgen)
    (_pureTermination :
        {t : β -> Nat // ∀ b, ⦃⌜ True ⌝⦄ termination b ⦃⇓ r => ⌜ r = Int.ofNat (t b) ⌝⦄} := by
      constructor; intro; mvcgen)
    (_pureCond :
        {c : β -> Bool // ∀ b, ⦃⌜ pureInv.val b ⌝⦄ cond b ⦃⇓ r => ⌜ r = c b ⌝⦄} := by
      constructor; intro; mvcgen) : RustM (Rust_primitives.Hax.LoopReturn γ β) := do
  let mut state := init
  for _ in [0 : 1 <<< 24] do
    let c ← cond state
    if !c then return .Continue state
    match (← body state) with
    | .Continue next => state := next
    | .Break ret => return .Break ret
  return .Continue state

@[spec]
theorem Rust_primitives.Hax.while_loop.spec {β : Type}
    (inv: β → RustM Prop)
    (cond: β → RustM Bool)
    (termination: β → RustM Hax_lib.Int.Int)
    (init : β)
    (body : β -> RustM β)
    (pureInv: {i : β -> Prop // ∀ b, ⦃⌜ True ⌝⦄ inv b ⦃⇓ r => ⌜ r = (i b) ⌝⦄})
    (pureTermination :
      {t : β -> Nat // ∀ b, ⦃⌜ True ⌝⦄ termination b ⦃⇓ r => ⌜ r = Int.ofNat (t b) ⌝⦄})
    (pureCond : {c : β -> Bool // ∀ b, ⦃⌜ pureInv.val b ⌝⦄ cond b ⦃⇓ r => ⌜ r = c b ⌝⦄})
    (step :
      ∀ (b : β), pureCond.val b →
        ⦃⌜ pureInv.val b ⌝⦄
          body b
        ⦃⇓ b' => spred(⌜ pureTermination.val b' < pureTermination.val b ⌝ ∧ ⌜ pureInv.val b' ⌝)⦄ ) :
    ⦃⌜ pureInv.val init ⌝⦄
      while_loop inv cond termination init body pureInv pureTermination pureCond
    ⦃⇓ r => ⌜ pureInv.val r ∧ ¬ pureCond.val r ⌝⦄ :=
  Spec.MonoLoopCombinator.while_loop init Loop.mk pureCond.val body pureInv pureTermination step
