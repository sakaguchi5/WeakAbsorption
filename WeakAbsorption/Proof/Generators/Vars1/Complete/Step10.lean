import WeakAbsorption.Proof.Generators.Vars1.Complete.Step9
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step3
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step4

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step10

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step3
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step7
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step8
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step9

/-!
Step10 (SAFE): Final packaging for vars=1 completion above K≥11.

What Step10 does (and does NOT do):

- It does NOT prove the hard lemma `GapImpliesKindAt R K`.
- Instead, it packages the whole pipeline so that:

    If you prove `GapImpliesKindAt` for the relevant rule sets (and K≥11),
    then for every K≥11:
      * there exist actual gap instances (Step3),
      * and each such gap instance is classified by the finite core templates (Step7/8/9).

This turns Step11 into a single-target job: prove `GapImpliesKindAt`.
-/

section

-- ============================================================
-- 10.1  Convert Step3's NormalForm-level gaps to Step4's Term-level gaps
-- ============================================================

/--
From a NormalForm-level gap witness (Step3.GapAt),
we can produce a Term-level gap witness (Step4.GapTermAt) by taking underlying terms.
-/
theorem exists_gapTermAt_of_gapAt (R : RuleSet) (K : Nat) :
  GapAt (R := R) K → ∃ u v : Term V, GapTermAt (R := R) K u v := by
  intro h
  rcases h with ⟨x, y, hxK, hyK, hRel, hNot⟩
  refine ⟨x.1, y.1, ?_⟩
  refine ⟨x, y, rfl, rfl, hxK, hyK, hRel, hNot⟩

/--
Concrete existence: for any K≥11, there exists a Term-level gap at R=[].
-/
theorem exists_gapTermAt_nil_of_K_ge_11 (K : Nat) (hK : 11 ≤ K) :
  ∃ u v : Term V, GapTermAt (R := ([] : RuleSet)) K u v := by
  have hNF : GapAt (R := ([] : RuleSet)) K := gapAt_nil_of_K_ge_11 (K := K) hK
  exact exists_gapTermAt_of_gapAt (R := ([] : RuleSet)) (K := K) hNF

/--
Concrete existence: for any K≥11, there exists a Term-level gap at R=[SqAbsorb].
-/
theorem exists_gapTermAt_sqAbsorb_of_K_ge_11 (K : Nat) (hK : 11 ≤ K) :
  ∃ u v : Term V, GapTermAt (R := ([RuleId.SqAbsorb] : RuleSet)) K u v := by
  have hNF : GapAt (R := ([RuleId.SqAbsorb] : RuleSet)) K :=
    gapAt_sqAbsorb_of_K_ge_11 (K := K) hK
  exact exists_gapTermAt_of_gapAt (R := ([RuleId.SqAbsorb] : RuleSet)) (K := K) hNF

-- ============================================================
-- 10.2  The “one thing to prove” form: GapImpliesKindAt (K≥11) for two rule sets
-- ============================================================

/--
Step11 target (K≥11, R=[]): raw gaps’ canonical cores are classifiable (some kind).
-/
def GapImpliesKindAt_nil_ge11 : Prop :=
  ∀ K : Nat, 11 ≤ K → GapImpliesKindAt (R := ([] : RuleSet)) K

/--
Step11 target (K≥11, R=[SqAbsorb]): raw gaps’ canonical cores are classifiable (some kind).
-/
def GapImpliesKindAt_sqAbsorb_ge11 : Prop :=
  ∀ K : Nat, 11 ≤ K → GapImpliesKindAt (R := ([RuleId.SqAbsorb] : RuleSet)) K

/--
Bundled “vars=1 completion target” for Step11.
-/
def Vars1CompletionTarget : Prop :=
  GapImpliesKindAt_nil_ge11 ∧ GapImpliesKindAt_sqAbsorb_ge11

-- ============================================================
-- 10.3  If Step11 target holds, then every K≥11 gap is classified by the finite kernels
-- ============================================================

/--
If `GapImpliesKindAt` holds for (R,K), then every Term-level gap instance has a concrete kind value
(sqAbsorb or sqStable) on its canonical core.
-/
theorem gapKindValue_of_gapImpliesKindAt
  (R : RuleSet) (K : Nat)
  (hKind : GapImpliesKindAt (R := R) K) :
  ∀ u v : Term V, GapTermAt (R := R) K u v →
    (getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
    ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable) := by
  -- Step8 already gives exactly this corollary
  exact GapCoreKindValueAt_of_GapImpliesKindAt (R := R) (K := K) hKind

/--
Concrete classification existence (R=[]):

If Step11's R=[] target holds, then for every K≥11 there exists a gap (u,v) whose canonical core
is classified as sqAbsorb or sqStable.
-/
theorem exists_classified_gap_nil
  (hNil : GapImpliesKindAt_nil_ge11) :
  ∀ K : Nat, 11 ≤ K →
    ∃ u v : Term V,
      GapTermAt (R := ([] : RuleSet)) K u v ∧
      ((getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
        ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable)) := by
  intro K hK
  rcases exists_gapTermAt_nil_of_K_ge_11 (K := K) hK with ⟨u, v, hGap⟩
  have hKind : GapImpliesKindAt (R := ([] : RuleSet)) K := hNil K hK
  refine ⟨u, v, hGap, ?_⟩
  -- classify this concrete gap via Step8 corollary
  exact gapKindValue_of_gapImpliesKindAt (R := ([] : RuleSet)) (K := K) hKind u v hGap

/--
Concrete classification existence (R=[SqAbsorb]):

If Step11's R=[SqAbsorb] target holds, then for every K≥11 there exists a gap (u,v)
whose canonical core is classified.
-/
theorem exists_classified_gap_sqAbsorb
  (hAbs : GapImpliesKindAt_sqAbsorb_ge11) :
  ∀ K : Nat, 11 ≤ K →
    ∃ u v : Term V,
      GapTermAt (R := ([RuleId.SqAbsorb] : RuleSet)) K u v ∧
      ((getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
        ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable)) := by
  intro K hK
  rcases exists_gapTermAt_sqAbsorb_of_K_ge_11 (K := K) hK with ⟨u, v, hGap⟩
  have hKind : GapImpliesKindAt (R := ([RuleId.SqAbsorb] : RuleSet)) K := hAbs K hK
  refine ⟨u, v, hGap, ?_⟩
  exact gapKindValue_of_gapImpliesKindAt (R := ([RuleId.SqAbsorb] : RuleSet)) (K := K) hKind u v hGap

/--
Final Step10 summary theorem:

Assuming `Vars1CompletionTarget`, then for every K≥11:
- there exists a classified gap at R=[],
- there exists a classified gap at R=[SqAbsorb].

This is the clean “everything except Step11 is done” statement.
-/
theorem vars1_completion_summary
  (h : Vars1CompletionTarget) :
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
  rcases h with ⟨hNil, hAbs⟩
  refine ⟨?_, ?_⟩
  · exact exists_classified_gap_nil (hNil := hNil) K hK
  · exact exists_classified_gap_sqAbsorb (hAbs := hAbs) K hK

end

end Step10
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
