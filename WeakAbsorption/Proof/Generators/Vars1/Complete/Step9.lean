import WeakAbsorption.Proof.Generators.Vars1.Complete.Step8

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step9

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step6
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step7
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step8

/-!
Step9 (SAFE): Normalize the remaining obligation by proving equivalences.

After Step8, the remaining “vars=1 completion” task can be stated in several forms:

  (A) GapImpliesOrbitAt  : GapTermAt R K u v → Vars1OrbitTpl u v
  (B) GapCoreTplAt       : GapTermAt R K u v → Vars1CoreTpl (coreU u v) (coreV u v)
  (C) GapImpliesKindAt   : GapTermAt R K u v → ∃k, getCoreKind? (coreU u v) (coreV u v) = some k

This file proves (A) ↔ (B) ↔ (C).  Hence, Step10 only needs to prove one of them.
-/

section

-- ============================================================
-- 9.1  (B) ↔ (C): core-template ↔ classifier “some”
-- ============================================================

/-- GapCoreTplAt implies GapImpliesKindAt (choose k by classifier value lemma). -/
theorem GapImpliesKindAt_of_GapCoreTplAt (R : RuleSet) (K : Nat) :
  GapCoreTplAt (R := R) K → GapImpliesKindAt (R := R) K := by
  intro hCore
  intro u v hGap
  have hTpl : Step1.Vars1CoreTpl (coreU u v) (coreV u v) := hCore u v hGap
  -- Step7 gives: template ⇒ classifier returns some sqAbsorb or some sqStable
  have hv : (getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
          ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable) :=
    getCoreKind?_value_of_coreTpl (u := coreU u v) (v := coreV u v) hTpl
  cases hv with
  | inl hA =>
      exact ⟨Vars1CoreKind.sqAbsorb, hA⟩
  | inr hS =>
      exact ⟨Vars1CoreKind.sqStable, hS⟩

/-- GapImpliesKindAt implies GapCoreTplAt (classifier completeness). -/
theorem GapCoreTplAt_of_GapImpliesKindAt (R : RuleSet) (K : Nat) :
  GapImpliesKindAt (R := R) K → GapCoreTplAt (R := R) K := by
  intro hKind
  intro u v hGap
  rcases hKind u v hGap with ⟨k, hk⟩
  exact of_getCoreKind? (u := coreU u v) (v := coreV u v) (k := k) hk

/-- (B) ↔ (C) packaged. -/
theorem GapCoreTplAt_iff_GapImpliesKindAt (R : RuleSet) (K : Nat) :
  GapCoreTplAt (R := R) K ↔ GapImpliesKindAt (R := R) K := by
  constructor
  · exact GapImpliesKindAt_of_GapCoreTplAt (R := R) (K := K)
  · exact GapCoreTplAt_of_GapImpliesKindAt (R := R) (K := K)

-- ============================================================
-- 9.2  (A) ↔ (B): orbit bridge ↔ canonical core template
-- ============================================================

/--
GapCoreTplAt implies GapImpliesOrbitAt:

If the canonical core is a template, Step5 yields orbit directly (canonical fuel).
-/
theorem GapImpliesOrbitAt_of_GapCoreTplAt (R : RuleSet) (K : Nat) :
  GapCoreTplAt (R := R) K → GapImpliesOrbitAt (R := R) K := by
  intro hCore
  intro u v hGap
  have hTpl : Step1.Vars1CoreTpl (coreU u v) (coreV u v) := hCore u v hGap
  -- Step5: canonical core template ⇒ orbit
  exact orbit_of_coreFuel_coreTpl (u := u) (v := v) (hTpl := hTpl)

/--
GapImpliesOrbitAt implies GapCoreTplAt:

This is Step6’s main bridge: orbit ⇒ canonical core template.
-/
theorem GapCoreTplAt_of_GapImpliesOrbitAt (R : RuleSet) (K : Nat) :
  GapImpliesOrbitAt (R := R) K → GapCoreTplAt (R := R) K := by
  intro hOrbit
  -- Step6 already gives exactly this transformation
  exact GapCoreTplAt_of_gapImpliesOrbit (R := R) (K := K) hOrbit

/-- (A) ↔ (B) packaged. -/
theorem GapImpliesOrbitAt_iff_GapCoreTplAt (R : RuleSet) (K : Nat) :
  GapImpliesOrbitAt (R := R) K ↔ GapCoreTplAt (R := R) K := by
  constructor
  · exact GapCoreTplAt_of_GapImpliesOrbitAt (R := R) (K := K)
  · exact GapImpliesOrbitAt_of_GapCoreTplAt (R := R) (K := K)

-- ============================================================
-- 9.3  Full normalization: (A) ↔ (B) ↔ (C)
-- ============================================================

/-- All three remaining formulations are equivalent. -/
theorem GapCompletionForms_equiv (R : RuleSet) (K : Nat) :
  (GapImpliesOrbitAt (R := R) K)
    ↔ (GapCoreTplAt (R := R) K)
    ∧ (GapImpliesKindAt (R := R) K) := by
  constructor
  · intro hA
    have hB : GapCoreTplAt (R := R) K := (GapCoreTplAt_of_GapImpliesOrbitAt (R := R) (K := K)) hA
    have hC : GapImpliesKindAt (R := R) K := (GapImpliesKindAt_of_GapCoreTplAt (R := R) (K := K)) hB
    exact ⟨hB, hC⟩
  · intro h
    rcases h with ⟨hB, _hC⟩
    exact (GapImpliesOrbitAt_of_GapCoreTplAt (R := R) (K := K)) hB

/-
Step10 (the next hard step) now has a clean choice:

You only need to prove ONE of:
  - GapImpliesOrbitAt R K
  - GapCoreTplAt R K
  - GapImpliesKindAt R K

and Step9 gives the other two for free.

The “safest” target is often GapCoreTplAt, because it talks only about the canonical core
(coreU/coreV) and uses no orbit reasoning in the proof goal.
-/

end

end Step9
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
