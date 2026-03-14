import WeakAbsorption.Core.Canonical
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step10
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step9
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step4

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step13

open WeakAbsorption
open WeakAbsorption.WAA
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck
open WeakAbsorption.Closure

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step7
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step8
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step9
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step10

/-!
Step13: Reduce the remaining obligations to ONE uniform lemma.

If we can prove (vars=1):

  NFRel x y  →  Vars1OrbitTpl x.1 y.1

for all normal forms x,y, then for ANY R,K:

  GapTermAt R K u v  →  Vars1OrbitTpl u v
  → GapCoreTplAt R K
  → GapImpliesKindAt R K

Hence Step10's `Vars1CompletionTarget` follows immediately.

So Step14/15 only need to prove this single lemma `NFRelImpliesOrbitAt`.
-/

section

-- ============================================================
-- 13.1  The single remaining “content lemma”
-- ============================================================

/--
The ONE lemma that would close everything:

vars=1: NFRel between normal forms always produces an orbit instance.
-/
def NFRelImpliesOrbitAt : Prop :=
  ∀ x y : NormalForm V, x.1 ≠ y.1 → NFRel (α := V) x y → Vars1OrbitTpl x.1 y.1
-- ============================================================
-- 13.2  From NFRel⇒orbit to raw gap⇒orbit (for any R,K)
-- ============================================================

theorem gapImpliesOrbitAt_of_NFRelImpliesOrbitAt
  (R : RuleSet) (K : Nat)
  (hNF : NFRelImpliesOrbitAt) :
  GapImpliesOrbitAt (R := R) K := by
  intro u v hGap
  rcases hGap with ⟨x, y, hu, hv, hxK, hyK, hRel, hNot⟩
  subst hu; subst hv
    -- gap から x.1 ≠ y.1 を作る（x=y なら NFEqR は refl で成立して gap と矛盾）
  have hne : x.1 ≠ y.1 := by
    intro hEq
    have hxy : x = y := Subtype.ext (by simpa using hEq)
    have href : NFEqR (α := V) R x x := by
      -- NFEqR R = EqvGen (NFStepR R)
      unfold WAA.NFEqR
      exact EqvGen.refl (r := NFStepR (α := V) R) x
    have : NFEqR (α := V) R x y := by
      simpa [hxy] using href
    exact hNot this

  exact hNF x y hne hRel

-- ============================================================
-- 13.3  Therefore, we get GapCoreTplAt and GapImpliesKindAt for free
-- ============================================================

theorem gapCoreTplAt_of_NFRelImpliesOrbitAt
  (R : RuleSet) (K : Nat)
  (hNF : NFRelImpliesOrbitAt) :
  GapCoreTplAt (R := R) K := by
  -- Step9: gap⇒orbit ↔ gap⇒coreTpl (canonical core)
  have hOrbit : GapImpliesOrbitAt (R := R) K :=
    gapImpliesOrbitAt_of_NFRelImpliesOrbitAt (R := R) (K := K) hNF
  exact (Step7.GapCoreTplAt_of_GapImpliesOrbitAt (R := R) (K := K)) hOrbit

theorem gapImpliesKindAt_of_NFRelImpliesOrbitAt
  (R : RuleSet) (K : Nat)
  (hNF : NFRelImpliesOrbitAt) :
  GapImpliesKindAt (R := R) K := by
  have hCore : GapCoreTplAt (R := R) K :=
    gapCoreTplAt_of_NFRelImpliesOrbitAt (R := R) (K := K) hNF
  exact (GapImpliesKindAt_of_GapCoreTplAt (R := R) (K := K)) hCore

-- ============================================================
-- 13.4  Step10 targets (K≥11) become immediate
-- ============================================================

theorem gapImpliesKind_nil_ge11_of_NFRelImpliesOrbitAt
  (hNF : NFRelImpliesOrbitAt) :
  GapImpliesKindAt_nil_ge11 := by
  intro K hK
  exact gapImpliesKindAt_of_NFRelImpliesOrbitAt (R := ([] : RuleSet)) (K := K) hNF

theorem gapImpliesKind_sqAbsorb_ge11_of_NFRelImpliesOrbitAt
  (hNF : NFRelImpliesOrbitAt) :
  GapImpliesKindAt_sqAbsorb_ge11 := by
  intro K hK
  exact gapImpliesKindAt_of_NFRelImpliesOrbitAt (R := ([RuleId.SqAbsorb] : RuleSet)) (K := K) hNF

theorem vars1CompletionTarget_of_NFRelImpliesOrbitAt
  (hNF : NFRelImpliesOrbitAt) :
  Vars1CompletionTarget :=
by
  refine ⟨?_, ?_⟩
  · exact gapImpliesKind_nil_ge11_of_NFRelImpliesOrbitAt hNF
  · exact gapImpliesKind_sqAbsorb_ge11_of_NFRelImpliesOrbitAt hNF

end

end Step13
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
