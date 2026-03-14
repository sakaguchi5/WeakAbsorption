import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Proof.Generators.Necessity.K11
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace WAA
namespace OrbitLeafParityStability

open WeakAbsorption.Spec
open WeakAbsorption.WAA.NecessityK11

section
variable {α : Type}

-- ------------------------------------------------------------
-- Bool helper lemmas (tiny and stable)
-- ------------------------------------------------------------

@[simp] private theorem xor_false_left (p : Bool) : Bool.xor false p = p := by
  cases p <;> rfl

@[simp] private theorem xor_false_right (p : Bool) : Bool.xor p false = p := by
  cases p <;> rfl

@[simp] private theorem xor_true_left (p : Bool) : Bool.xor true p = Bool.not p := by
  cases p <;> rfl

private theorem xor_true_xor (b p : Bool) :
  Bool.xor true (Bool.xor b p) = Bool.xor (Bool.not b) p := by
  cases b <;> cases p <;> rfl

private theorem xor_cancel_left (f p q : Bool) :
  Bool.xor f p = Bool.xor f q → p = q := by
  cases f <;> cases p <;> cases q <;> intro h <;> cases h <;> rfl

-- ------------------------------------------------------------
-- Flip computed from the *context*, not from the proof
-- (so no Prop-elimination issue)
-- ------------------------------------------------------------

/--
A computable “flip bit” extracted from a context.

We only *use* it under the hypothesis `SafeCtxR D`.
For other contexts, we return `false` arbitrarily.
-/
def ctxFlip : Ctx α → Bool
  | .hole => false
  | .right (Term.var _) C => Bool.not (ctxFlip C)
  | _ => false

@[simp] theorem ctxFlip_hole : ctxFlip (α := α) (.hole) = false := rfl

@[simp] theorem ctxFlip_rightVar (a : α) (C : Ctx α) :
  ctxFlip (α := α) (.right (Term.var a) C) = Bool.not (ctxFlip (α := α) C) := by
  rfl

-- ------------------------------------------------------------
-- Main orbit stability facts for SafeCtxR
-- ------------------------------------------------------------

/--
Main formula (Prop-safe):
for SafeCtxR contexts, plugging toggles leafParity by the fixed bit `ctxFlip D`.
-/
theorem SafeCtxR.leafParity_plug {D : Ctx α} (hD : SafeCtxR (α := α) D) (t : Term α) :
  leafParity (Ctx.plug D t) = Bool.xor (ctxFlip (α := α) D) (leafParity t) := by
  -- Induction on hD is allowed (target is Prop: equality of Bool)
  induction hD with
  | hole =>
      simp [Ctx.plug, ctxFlip]
  | rightVar a hC ih =>
      -- D = right (var a) C
      -- plug D t = (var a) ⋆ plug C t
      -- leafParity = xor true (leafParity (plug C t))
      -- and IH gives leafParity (plug C t) = xor (ctxFlip C) (leafParity t)
      simp [Ctx.plug, leafParity, ctxFlip, ih]

/--
SafeCtxR preserves parity *equality* (and hence inequality) between two terms.
This is the orbit-stability statement you actually want.
-/
theorem SafeCtxR.leafParity_eq_iff {D : Ctx α} (hD : SafeCtxR (α := α) D) (t u : Term α) :
  leafParity (Ctx.plug D t) = leafParity (Ctx.plug D u) ↔ leafParity t = leafParity u := by
  constructor
  · intro h
    have hx :
      Bool.xor (ctxFlip (α := α) D) (leafParity t)
        = Bool.xor (ctxFlip (α := α) D) (leafParity u) := by
      simpa [SafeCtxR.leafParity_plug (α := α) hD] using h
    exact xor_cancel_left (ctxFlip (α := α) D) (leafParity t) (leafParity u) hx
  · intro h
    have :
      Bool.xor (ctxFlip (α := α) D) (leafParity t)
        = Bool.xor (ctxFlip (α := α) D) (leafParity u) := by
      simp [h]
    simpa [SafeCtxR.leafParity_plug (α := α) hD] using this

/--
Orbit stability theorem (SqAbsorb-only):

If two NormalForms have different leafParity, then **no SafeCtxR orbit variant**
can become connected by `NFEqR [SqAbsorb]`.

This is the precise “orbit安定性” completion for the SqAbsorb-only obstruction.
-/
theorem not_NFEqR_sqAbsorb_orbit_of_leafParity_ne
  {D : Ctx α} (hD : SafeCtxR (α := α) D)
  {x y : NormalForm α} (hne : leafParity x.1 ≠ leafParity y.1) :
  ¬ NFEqR (α := α) ([RuleId.SqAbsorb] : RuleSet)
      (plugNF (α := α) D x (SafeCtxR.dom (α := α) hD x))
      (plugNF (α := α) D y (SafeCtxR.dom (α := α) hD y)) := by
  intro h
  -- SqAbsorb-only preserves leafParity on NormalForms (from NecessityK11)
  have hpar :=
    NFEqR_sqAbsorb_preserves_leafParity (α := α)
      (x := plugNF (α := α) D x (SafeCtxR.dom (α := α) hD x))
      (y := plugNF (α := α) D y (SafeCtxR.dom (α := α) hD y))
      h

  -- unwrap to parity equality on plugged underlying terms
  have hplug : leafParity (Ctx.plug D x.1) = leafParity (Ctx.plug D y.1) := by
    simpa [plugNF] using hpar

  -- cancel the common ctxFlip to get leafParity x = leafParity y
  have : leafParity x.1 = leafParity y.1 := by
    exact (SafeCtxR.leafParity_eq_iff (α := α) hD x.1 y.1).1 hplug

  exact hne this

end

end OrbitLeafParityStability
end WAA
end WeakAbsorption
