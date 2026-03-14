import WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
import WeakAbsorption.Proof.Generators.Necessity.K11
import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Core.Measure
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step3

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck
open WeakAbsorption.WAA
open WeakAbsorption.WAA.NecessityK11
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2

/-!
Step3 (SAFE): K-general necessity + a clean “pipeline interface”.

We do NOT classify all vars=1 NormalForms here.

What we *can* finish safely:

(1) K-general necessity:
    - For any K ≥ 11, there exists an NFRel pair (size ≤ K) not connected by R=[].
    - For any K ≥ 11, there exists an NFRel pair (size ≤ K) not connected by R=[SqAbsorb].

(2) A reusable interface:
    If some predicate P(u,v) implies the orbit predicate Vars1OrbitTpl u v,
    then P(u,v) implies “after stripping with some fuel, the core is in Vars1CoreTpl”.

This sets up Step4, where we choose P to be the “real target predicate”
(e.g. a proof-side version of the gap predicate you care about).
-/

section

-- ============================================================
-- 3.1  A simple “connects all NFRel pairs up to size K” predicate
-- ============================================================

/--
`ConnectsAll R K` means:
for any NormalForms x,y with size ≤ K, if NFRel x y then NFEqR R x y.
-/
def ConnectsAll (R : RuleSet) (K : Nat) : Prop :=
  ∀ x y : NormalForm V,
    size x.1 ≤ K →
    size y.1 ≤ K →
    NFRel (α := V) x y →
    NFEqR (α := V) R x y

/--
`GapAt R K` means:
there exist NormalForms x,y of size ≤ K that are NFRel but not connected by NFEqR R.
-/
def GapAt (R : RuleSet) (K : Nat) : Prop :=
  ∃ x y : NormalForm V,
    size x.1 ≤ K ∧ size y.1 ≤ K ∧
    NFRel (α := V) x y ∧
    ¬ NFEqR (α := V) R x y

theorem gapAt_of_not_connectsAll (R : RuleSet) (K : Nat) :
  (¬ ConnectsAll R K) → GapAt R K := by
  intro h
  -- classical: contraposition is not worth it; build directly using the negation witness
  -- We unfold ¬ConnectsAll and pull out a counterexample.
  -- Lean: use classical choice from `not_forall`.
  classical
  -- Expand the negation and extract a witness.
  -- (We keep it explicit to stay mathlib-free.)
  unfold ConnectsAll at h
  -- h : ¬ ∀ (x y : ...), ...
  -- 1. 「すべての...ではない」を「ある...が存在して、～ではない」に変換
  rw [Classical.not_forall] at h
  rcases h with ⟨x, h⟩
  -- 2. 同様に y についても否定を内側に入れる
  rw [Classical.not_forall] at h
  rcases h with ⟨y, h⟩
  -- 3. さらに含意 (P → Q → R → ...) の否定をバラす
  -- ¬(P → Q) は P ∧ ¬Q であることを利用
  rw [not_imp] at h
  rcases h with ⟨hxK, h⟩

  rw [not_imp] at h
  rcases h with ⟨hyK, h⟩

  rw [not_imp] at h
  rcases h with ⟨hrel, hnot⟩

  -- 最終的に目的の形が取り出せる
  exact ⟨x, y, hxK, hyK, hrel, hnot⟩

-- ============================================================
-- 3.2  K-general necessity (lift K=11 witnesses to any K ≥ 11)
-- ============================================================

/--
SqAbsorb is necessary at any K ≥ 11, in the minimal sense that R=[] fails to connect all NFRel pairs.
-/
theorem not_connectsAll_nil_of_K_ge_11 (K : Nat) (hK : 11 ≤ K) :
  ¬ ConnectsAll ([] : RuleSet) K := by
  intro hconn
  -- Use the K=11 witness from NecessityK11
  have hw := sqAbsorb_is_necessary_K11 (α := V) (a := (0 : V))
  rcases hw with ⟨x, y, hne, hx11, hy11, hrel, hnot⟩
  have hxK : size x.1 ≤ K := Nat.le_trans hx11 hK
  have hyK : size y.1 ≤ K := Nat.le_trans hy11 hK
  have hxy : NFEqR (α := V) ([] : RuleSet) x y := hconn x y hxK hyK hrel
  exact hnot hxy

theorem gapAt_nil_of_K_ge_11 (K : Nat) (hK : 11 ≤ K) :
  GapAt ([] : RuleSet) K := by
  have : ¬ ConnectsAll ([] : RuleSet) K := not_connectsAll_nil_of_K_ge_11 (K := K) hK
  exact gapAt_of_not_connectsAll ([] : RuleSet) K this

/--
SqStable is necessary after SqAbsorb at any K ≥ 11, in the sense that R=[SqAbsorb] fails.
-/
theorem not_connectsAll_sqAbsorb_of_K_ge_11 (K : Nat) (hK : 11 ≤ K) :
  ¬ ConnectsAll ([RuleId.SqAbsorb] : RuleSet) K := by
  intro hconn
  have hw := sqStable_is_necessary_after_sqAbsorb_K11 (α := V) (a := (0 : V))
  rcases hw with ⟨x, y, hx11, hy11, hrel, hnot⟩
  have hxK : size x.1 ≤ K := Nat.le_trans hx11 hK
  have hyK : size y.1 ≤ K := Nat.le_trans hy11 hK
  have hxy : NFEqR (α := V) ([RuleId.SqAbsorb] : RuleSet) x y := hconn x y hxK hyK hrel
  exact hnot hxy

theorem gapAt_sqAbsorb_of_K_ge_11 (K : Nat) (hK : 11 ≤ K) :
  GapAt ([RuleId.SqAbsorb] : RuleSet) K := by
  have : ¬ ConnectsAll ([RuleId.SqAbsorb] : RuleSet) K :=
    not_connectsAll_sqAbsorb_of_K_ge_11 (K := K) hK
  exact gapAt_of_not_connectsAll ([RuleId.SqAbsorb] : RuleSet) K this

-- ============================================================
-- 3.3  A reusable “pipeline interface”: P → orbit → core template
-- ============================================================

/--
Existential-fuel coverage interface (term-level):

`CoveredByExists P T` means:
if P(u,v) holds, then for some fuel, the stripped core of (u,v) is in template T.
-/
def CoveredByExists (P : Term V → Term V → Prop) (T : Step0.CoreTpl V) : Prop :=
  ∀ u v : Term V,
    P u v →
    ∃ fuel,
      let d := Step0.decomp (α := V) fuel u v
      T d.u0 d.v0

/--
Main pipeline lemma:

If P(u,v) implies Vars1OrbitTpl u v, then P is covered (∃fuel) by Vars1CoreTpl.
-/
theorem coveredByExists_of_orbit
  (P : Term V → Term V → Prop)
  (hPorbit : ∀ u v, P u v → Vars1OrbitTpl u v) :
  CoveredByExists P Step1.Vars1CoreTpl := by
  intro u v hP
  have horb : Vars1OrbitTpl u v := hPorbit u v hP
  -- Step2 gives the existential-fuel core-template result for orbit pairs
  exact coveredBy_templates_on_orbits_existsFuel (u := u) (v := v) horb

/-
Step4 will instantiate P with a proof-side predicate that genuinely characterizes
the “vars=1 phenomena you care about” (e.g., a proof-side gap predicate),
and will prove hPorbit: P → Vars1OrbitTpl.

Once that is done, Step2+Step3 immediately give:
- every P-instance reduces to one of the finite core templates (A↔s or Au↔A),
- and the K-general necessity results explain why SqAbsorb then SqStable must appear.
-/

end

end Step3
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
