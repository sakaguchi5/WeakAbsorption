import WeakAbsorption.Proof.Generators.Vars1.Complete.Step10

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step11

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step7
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step8
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step10

/-!
Step11 (SAFE): isolate the last two obligations and close the whole pipeline once they are proved.

At this stage, everything reduces to proving:

  (1) ∀K≥11, GapImpliesKindAt (R := []) K
  (2) ∀K≥11, GapImpliesKindAt (R := [SqAbsorb]) K

Once those two are established, Step10 gives the final classification existence statements
for all K≥11, and Step7/8/9 propagate to core templates, kinds, etc.

Why Step11 is isolated:
- proving (1)(2) requires analyzing the actual structure of NFRel vs NFEqR in vars=1,
  i.e. the real mathematical content.
- all the “plumbing” (orbit, sizeOffset/K-dynamics, stripMany canonical cores, classifier)
  is already finished and verified through Step10.
-/

section

-- ============================================================
-- 11.1  The two remaining obligations (as constants to be proved in Step12)
-- ============================================================

/--
OBLIGATION (R=[]): for every K≥11, any raw gap instance implies the canonical core is classifiable.
-/
axiom gapImpliesKind_nil_ge11 : GapImpliesKindAt_nil_ge11

/--
OBLIGATION (R=[SqAbsorb]): for every K≥11, any raw gap instance implies the canonical core is classifiable.
-/
axiom gapImpliesKind_sqAbsorb_ge11 : GapImpliesKindAt_sqAbsorb_ge11

/--
Bundled completion target:
once these axioms are replaced by proofs, vars=1 completion is fully proved.
-/
theorem vars1_completion_target : Vars1CompletionTarget :=
  And.intro gapImpliesKind_nil_ge11 gapImpliesKind_sqAbsorb_ge11

-- ============================================================
-- 11.2  Final “everything closes” theorem (for immediate use)
-- ============================================================

/--
Final conclusion (existential form, K≥11):

For every K≥11:
- there exists a gap at R=[] whose canonical core is classified by sqAbsorb or sqStable;
- there exists a gap at R=[SqAbsorb] whose canonical core is classified.

This is exactly Step10.vars1_completion_summary instantiated with Step11 obligations.
-/
theorem vars1_completion_summary_ge11 :
  ∀ K : Nat, 11 ≤ K →
    (∃ u v : Term V,
      GapTermAt (R := ([] : RuleSet)) K u v ∧
      ((getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
        ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable)))
    ∧
    (∃ u v : Term V,
      GapTermAt (R := ([RuleId.SqAbsorb] : RuleSet)) K u v ∧
      ((getCoreKind? (coreU u v) (coreV u v) = some .sqAbsorb)
        ∨ (getCoreKind? (coreU u v) (coreV u v) = some .sqStable))) :=
by
  -- Step10 already packaged this; Step11 supplies the target assumptions.
  exact Step10.vars1_completion_summary (h := vars1_completion_target)

end

end Step11
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
