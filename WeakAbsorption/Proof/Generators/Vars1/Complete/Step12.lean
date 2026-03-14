import WeakAbsorption.Proof.Generators.Vars1.Complete.Step11
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step9

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step12

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step7
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step8
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step9
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step10
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step11

/-!
Step12 (SAFE skeleton): prove the two remaining obligations by reducing them to a small core lemma.

Goal (eventual):
  gapImpliesKind_nil_ge11       : ∀K≥11, GapImpliesKindAt (R:=[]) K
  gapImpliesKind_sqAbsorb_ge11  : ∀K≥11, GapImpliesKindAt (R:=[SqAbsorb]) K

We do NOT attempt a full NormalForm classification.
Instead, we:
- rewrite goals via Step9 equivalences,
- reduce everything to showing that the canonical core (coreU/coreV) must lie in Vars1CoreTpl
  whenever a gap exists.

The only genuinely hard content is isolated as a single lemma `coreTpl_of_gap`.
-/

section

-- ============================================================
-- 12.1  Turn “GapImpliesKindAt” into the more convenient “GapCoreTplAt”
-- ============================================================

theorem gapImpliesKind_of_gapCoreTpl (R : RuleSet) (K : Nat) :
  GapCoreTplAt (R := R) K → GapImpliesKindAt (R := R) K := by
  intro h
  -- Step9: (B) ↔ (C)
  exact (GapCoreTplAt_iff_GapImpliesKindAt (R := R) (K := K)).1 h

theorem gapCoreTpl_of_gapImpliesKind (R : RuleSet) (K : Nat) :
  GapImpliesKindAt (R := R) K → GapCoreTplAt (R := R) K := by
  intro h
  exact (GapCoreTplAt_iff_GapImpliesKindAt (R := R) (K := K)).2 h

-- ============================================================
-- 12.2  The single remaining “mathematical content” lemma
-- ============================================================

/-
This is the real heart:

For vars=1, any raw gap instance forces the canonical core to be one of the finite templates.

Once you prove this lemma for R=[] and R=[SqAbsorb] (for K≥11),
the rest is automatic by the plumbing already completed.
-/

axiom coreTpl_of_gap_nil_ge11 :
  ∀ K : Nat, 11 ≤ K →
    GapCoreTplAt (R := ([] : RuleSet)) K

axiom coreTpl_of_gap_sqAbsorb_ge11 :
  ∀ K : Nat, 11 ≤ K →
    GapCoreTplAt (R := ([RuleId.SqAbsorb] : RuleSet)) K

-- ============================================================
-- 12.3  Close Step11 obligations (replace axioms later by proofs)
-- ============================================================

/-- Replace Step11's axiom `gapImpliesKind_nil_ge11` by a proof, once `coreTpl_of_gap_nil_ge11` is proved. -/
theorem gapImpliesKind_nil_ge11_proved :
  GapImpliesKindAt_nil_ge11 := by
  intro K hK
  -- from GapCoreTplAt to GapImpliesKindAt via Step9
  exact gapImpliesKind_of_gapCoreTpl (R := ([] : RuleSet)) (K := K)
    (coreTpl_of_gap_nil_ge11 K hK)

/-- Replace Step11's axiom `gapImpliesKind_sqAbsorb_ge11` by a proof, once `coreTpl_of_gap_sqAbsorb_ge11` is proved. -/
theorem gapImpliesKind_sqAbsorb_ge11_proved :
  GapImpliesKindAt_sqAbsorb_ge11 := by
  intro K hK
  exact gapImpliesKind_of_gapCoreTpl (R := ([RuleId.SqAbsorb] : RuleSet)) (K := K)
    (coreTpl_of_gap_sqAbsorb_ge11 K hK)

/-- Therefore, once the two core lemmas are proved, the full Vars1CompletionTarget is proved. -/
theorem vars1_completion_target_proved : Vars1CompletionTarget :=
  And.intro gapImpliesKind_nil_ge11_proved gapImpliesKind_sqAbsorb_ge11_proved

/--
Final: the Step10 summary theorem becomes unconditional once the two core lemmas are proved.
(At the moment it is conditional on the two axioms above.)
-/
theorem vars1_completion_summary_ge11_proved :
  ∀ K : Nat, 11 ≤ K →
    (∃ u v : Term V,
      GapTermAt (R := ([] : RuleSet)) K u v ∧
      ((getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
        ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable)))
    ∧
    (∃ u v : Term V,
      GapTermAt (R := ([RuleId.SqAbsorb] : RuleSet)) K u v ∧
      ((getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
        ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable))) := by
  intro K hK
  -- Step10 closes from the completion target
  exact Step10.vars1_completion_summary (h := vars1_completion_target_proved) K hK

end

end Step12
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
