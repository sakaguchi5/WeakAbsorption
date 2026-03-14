import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Proof.Generators.Orbit.Families.HoleLeftVar.Defs
import WeakAbsorption.Proof.Generators.Necessity.K11
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace WAA
namespace OrbitLeafParityStabilityHoleLeftVar

open WeakAbsorption.Spec
open WeakAbsorption.WAA.NecessityK11   -- leafParity, NFEqR_sqAbsorb_preserves_leafParity
open OrbitSafeHoleLeftVar

section
variable {α : Type}

/-! ############################################################
## ctxFlip 方式（Ctx → Bool）を □⋆x 側でも使う
############################################################ -/

/--
`ctxFlipAll C` = 文脈 `C` が（穴に挿す項と独立に）leafParity に与える “オフセット”。

狙い：常に
  leafParity (plug C t) = xor (ctxFlipAll C) (leafParity t)
を満たすように定義する。
-/
def ctxFlipAll : Ctx α → Bool
  | .hole        => false
  | .left C r    => Bool.xor (ctxFlipAll C) (leafParity r)
  | .right l C   => Bool.xor (leafParity l) (ctxFlipAll C)

/-- Main formula: plugging under any context is xor by a fixed offset. -/
theorem leafParity_plug_ctxFlipAll (C : Ctx α) (t : Term α) :
  leafParity (Ctx.plug C t) = Bool.xor (ctxFlipAll (α := α) C) (leafParity t) := by
  induction C with
  | hole =>
      simp [ctxFlipAll, Ctx.plug]
  | left C r ih =>
      -- plug (left C r) t = (plug C t) ⋆ r
      -- leafParity = xor (leafParity (plug C t)) (leafParity r)
      -- then use IH and AC of xor
      simp [ctxFlipAll, Ctx.plug, leafParity, ih, Bool.xor_left_comm, Bool.xor_comm]
  | right l C ih =>
      -- plug (right l C) t = l ⋆ (plug C t)
      simp [ctxFlipAll, Ctx.plug, leafParity, ih, Bool.xor_left_comm, Bool.xor_comm]

private theorem xor_cancel_left (f p q : Bool) :
  Bool.xor f p = Bool.xor f q → p = q := by
  cases f <;> cases p <;> cases q <;> intro h <;> cases h <;> rfl

/-- Parity equality is preserved (and reflected) by plugging under any fixed context. -/
theorem leafParity_eq_iff_plug (C : Ctx α) (t u : Term α) :
  leafParity (Ctx.plug C t) = leafParity (Ctx.plug C u) ↔ leafParity t = leafParity u := by
  constructor
  · intro h
    have hx :
        Bool.xor (ctxFlipAll (α := α) C) (leafParity t)
      = Bool.xor (ctxFlipAll (α := α) C) (leafParity u) := by
        simpa [leafParity_plug_ctxFlipAll (α := α) C] using h
    exact xor_cancel_left (ctxFlipAll (α := α) C) (leafParity t) (leafParity u) hx
  · intro h
    have :
        Bool.xor (ctxFlipAll (α := α) C) (leafParity t)
      = Bool.xor (ctxFlipAll (α := α) C) (leafParity u) := by
        simp [h]
    simpa [leafParity_plug_ctxFlipAll (α := α) C] using this

/-! ############################################################
## □⋆x（holeLeftVar）に特化：orbit安定性（SqAbsorb-only）
############################################################ -/

/-- For `□⋆a`, the offset is `true` (it flips parity). -/
theorem ctxFlipAll_holeLeftVar (a : α) :
  ctxFlipAll (α := α) (holeLeftVar (α := α) a) = true := by
  -- holeLeftVar a = left hole (var a)
  simp [holeLeftVar, ctxFlipAll, leafParity]

/--
Orbit stability theorem for `□⋆a`:

If two NormalForms have different leafParity, then even after plugging both sides into `□⋆a`
(the partial action’s “visible” side), they still cannot become connected by SqAbsorb-only NFEqR.

Note: this statement only needs normality of the *plugged* endpoints (to form `plugNF`).
-/
theorem not_NFEqR_sqAbsorb_holeLeftVar_of_leafParity_ne
  (a : α) {x y : NormalForm α}
  (hx : Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) x.1))
  (hy : Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) y.1))
  (hne : leafParity x.1 ≠ leafParity y.1) :
  ¬ NFEqR (α := α) ([RuleId.SqAbsorb] : RuleSet)
      (plugNF (α := α) (holeLeftVar (α := α) a) x hx)
      (plugNF (α := α) (holeLeftVar (α := α) a) y hy) := by
  intro h
  -- SqAbsorb-only preserves leafParity on NormalForms
  have hpar :=
    NFEqR_sqAbsorb_preserves_leafParity (α := α)
      (x := plugNF (α := α) (holeLeftVar (α := α) a) x hx)
      (y := plugNF (α := α) (holeLeftVar (α := α) a) y hy)
      h
  -- unwrap to parity equality on the plugged terms
  have hplug : leafParity (Ctx.plug (holeLeftVar (α := α) a) x.1)
            = leafParity (Ctx.plug (holeLeftVar (α := α) a) y.1) := by
    simpa [plugNF] using hpar
  -- reflect equality back to the cores (cancelling ctxFlipAll)
  have : leafParity x.1 = leafParity y.1 :=
    (leafParity_eq_iff_plug (α := α) (holeLeftVar (α := α) a) x.1 y.1).1 hplug
  exact hne this

end

end OrbitLeafParityStabilityHoleLeftVar
end WAA
end WeakAbsorption
