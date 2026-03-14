import WeakAbsorption.Proof.Generators.Vars1.Complete.Step7

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step8

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step6
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step7

/-!
Step8 (Classifier route): Reduce `GapTermAt → Vars1OrbitTpl` to a single “kind” obligation.

Recall from Step5/Step6:
- If `Vars1CoreTpl (coreU u v) (coreV u v)` holds, then we can get `Vars1OrbitTpl u v`
  via `orbit_of_coreFuel_coreTpl`.
- Step7 provides a safe classifier:
    getCoreKind? : Term V → Term V → Option Vars1CoreKind
  and a completeness lemma:
    of_getCoreKind? : getCoreKind? u v = some k → Vars1CoreTpl u v

Therefore:
- It is enough to show that for any raw gap instance (u,v),
  the canonical core (coreU u v, coreV u v) is classified by getCoreKind?
  i.e. getCoreKind? ... = some k for some k.

This file packages that reduction and gives the resulting bridge:
  GapImpliesKindAt R K  →  GapImpliesOrbitAt R K.
-/

section

-- ============================================================
-- 8.1  The key obligation stated in the best shape for proof
-- ============================================================

/--
Classifier-form bridge obligation:

For a given (R,K), every raw gap instance has canonical core whose kind is decidable
as `some k` (sqAbsorb or sqStable).
-/
def GapImpliesKindAt (R : RuleSet) (K : Nat) : Prop :=
  ∀ u v : Term V, GapTermAt (R := R) K u v →
    ∃ k : Vars1CoreKind, getCoreKind? (coreU u v) (coreV u v) = some k

-- ============================================================
-- 8.2  Kind ⇒ Core template (for canonical coreU/coreV)
-- ============================================================

/--
If the classifier returns `some k` on the canonical core, then the canonical core is a template.
-/
theorem coreTpl_of_coreKind?
  (u v : Term V) :
  (∃ k : Vars1CoreKind, getCoreKind? (coreU u v) (coreV u v) = some k) →
  Vars1CoreTpl (coreU u v) (coreV u v) := by
  intro hk
  rcases hk with ⟨k, hk⟩
  exact of_getCoreKind? (u := coreU u v) (v := coreV u v) (k := k) hk

-- ============================================================
-- 8.3  Main Step8 bridge: GapImpliesKindAt ⇒ GapImpliesOrbitAt
-- ============================================================

/--
Classifier route:

If raw gaps imply “canonical core is classifiable (some k)”, then raw gaps imply orbit.
-/
theorem gapImpliesOrbit_of_gapImpliesKindAt
  (R : RuleSet) (K : Nat)
  (hKind : GapImpliesKindAt (R := R) K) :
  GapImpliesOrbitAt (R := R) K := by
  intro u v hGap
  have hk : ∃ k : Vars1CoreKind, getCoreKind? (coreU u v) (coreV u v) = some k :=
    hKind u v hGap
  have hTpl : Vars1CoreTpl (coreU u v) (coreV u v) :=
    coreTpl_of_coreKind? (u := u) (v := v) hk
  -- Step5: canonical core template ⇒ orbit
  exact orbit_of_coreFuel_coreTpl (u := u) (v := v) (hTpl := hTpl)

-- ============================================================
-- 8.4  “Everything closes” corollaries (once GapImpliesKindAt is proved)
-- ============================================================

/--
Once you prove `GapImpliesKindAt R K`, you immediately get the canonical core-template obligation.
-/
theorem GapCoreTplAt_of_GapImpliesKindAt
  (R : RuleSet) (K : Nat)
  (hKind : GapImpliesKindAt (R := R) K) :
  GapCoreTplAt (R := R) K := by
  -- Step7: GapCoreTplAt from gap⇒orbit
  have hOrbit : GapImpliesOrbitAt (R := R) K :=
    gapImpliesOrbit_of_gapImpliesKindAt (R := R) (K := K) hKind
  exact GapCoreTplAt_of_GapImpliesOrbitAt (R := R) (K := K) hOrbit

/--
And you also get that every raw gap’s canonical core has a concrete kind value.
-/
theorem GapCoreKindValueAt_of_GapImpliesKindAt
  (R : RuleSet) (K : Nat)
  (hKind : GapImpliesKindAt (R := R) K) :
  ∀ u v : Term V, GapTermAt (R := R) K u v →
    (getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
    ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable) := by
  intro u v hGap
  have hTpl : Vars1CoreTpl (coreU u v) (coreV u v) :=
    (GapCoreTplAt_of_GapImpliesKindAt (R := R) (K := K) hKind) u v hGap
  exact getCoreKind?_value_of_coreTpl (u := coreU u v) (v := coreV u v) hTpl

end

end Step8
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
