import WeakAbsorption.Proof.Generators.Vars1.Complete.Step3

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step4

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step3

/-!
Step4 (Candidate 2): choose P aligned with “gap” observations, safely.

We define a term-level gap predicate `GapTermAt` mirroring Step3's `GapAt` but on `Term`:
  there exist NormalForms x,y whose underlying terms are u,v, with NFRel x y and ¬NFEqR R x y,
  and both sizes are ≤ K.

Then we define the Step4 predicate:
  P_gapOrbit R K u v := GapTermAt R K u v ∧ Vars1OrbitTpl u v

This keeps Step4 safe:
- `P_gapOrbit → Vars1OrbitTpl` is immediate,
- so Step3's pipeline applies and yields core-template reduction.

What remains for Step5:
- show that the *raw* gap predicate (GapTermAt) implies Vars1OrbitTpl in vars=1.
  (That is the “complete” bridge from observation to orbit.)
-/

section

-- ============================================================
-- 4.1  A term-level gap predicate (K-bounded)
-- ============================================================

/--
`GapTermAt R K u v`:
u and v are the underlying terms of some normal forms x,y (size ≤ K),
with NFRel x y but ¬ NFEqR R x y.
-/
def GapTermAt (R : RuleSet) (K : Nat) (u v : Term V) : Prop :=
  ∃ x y : NormalForm V,
    u = x.1 ∧ v = y.1 ∧
    size x.1 ≤ K ∧ size y.1 ≤ K ∧
    NFRel (α := V) x y ∧
    ¬ NFEqR (α := V) R x y

/--
Step4 predicate for candidate 2 (safe form):
a K-bounded gap instance PLUS the orbit hypothesis.
-/
def P_gapOrbit (R : RuleSet) (K : Nat) (u v : Term V) : Prop :=
  GapTermAt (R := R) K u v ∧ Vars1OrbitTpl u v

-- ============================================================
-- 4.2  Pipeline: P_gapOrbit → ∃fuel core template
-- ============================================================

/-- `P_gapOrbit` trivially implies `Vars1OrbitTpl`. -/
theorem P_gapOrbit_to_orbit (R : RuleSet) (K : Nat) (u v : Term V) :
  P_gapOrbit (R := R) K u v → Vars1OrbitTpl u v := by
  intro h
  exact h.2

/--
Main Step4 payoff:
Any `P_gapOrbit` instance reduces (∃fuel) to the finite core templates.
-/
theorem coveredByExists_gapOrbit (R : RuleSet) (K : Nat) :
  CoveredByExists (P := fun u v => P_gapOrbit (R := R) K u v) Step1.Vars1CoreTpl :=
by
  -- Step3 provides the generic lemma: (P→orbit) ⇒ CoveredByExists P Vars1CoreTpl
  refine coveredByExists_of_orbit (P := fun u v => P_gapOrbit (R := R) K u v) ?_
  intro u v hP
  exact (P_gapOrbit_to_orbit (R := R) (K := K) (u := u) (v := v) hP)

/-- Convenient corollary form (unpack CoveredByExists). -/
theorem P_gapOrbit_core_existsFuel (R : RuleSet) (K : Nat) (u v : Term V) :
  P_gapOrbit (R := R) K u v →
  ∃ fuel,
    let d := Step0.decomp (α := V) fuel u v
    Step1.Vars1CoreTpl d.u0 d.v0 :=
by
  intro h
  exact (coveredByExists_gapOrbit (R := R) (K := K) u v h)

-- ============================================================
-- 4.3  What Step5 must prove (single clean obligation)
-- ============================================================

/--
Step5 obligation (the real “vars=1 complete” bridge):

If every raw gap instance is an orbit instance, i.e.
  GapTermAt R K u v → Vars1OrbitTpl u v,
then raw gaps are also covered by core templates.
-/
theorem coveredByExists_rawGap_of_gapImpliesOrbit
  (R : RuleSet) (K : Nat)
  (gapImpliesOrbit : ∀ u v, GapTermAt (R := R) K u v → Vars1OrbitTpl u v) :
  CoveredByExists (P := fun u v => GapTermAt (R := R) K u v) Step1.Vars1CoreTpl :=
by
  -- Use the pipeline with P := GapTermAt
  refine coveredByExists_of_orbit (P := fun u v => GapTermAt (R := R) K u v) ?_
  intro u v hGap
  exact gapImpliesOrbit u v hGap

end

end Step4
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
