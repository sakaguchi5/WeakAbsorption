import WeakAbsorption.Proof.Generators.Vars1.Complete.Step0
import WeakAbsorption.Proof.Generators.Necessity.K11
import WeakAbsorption.Tooling.SmallCheck.Phase0
import WeakAbsorption.Core.Measure
import WeakAbsorption.Core.Rewrite

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step1

open WeakAbsorption
open WeakAbsorption.WAA
open WeakAbsorption.Spec
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step0
open WeakAbsorption.Proof.Generators.StripLite

/-!
Step1: vars=1 core templates + first coverage theorem(s).

This file does NOT yet prove the full classification.
It introduces the finite set of core templates that Step2+ will show to be complete,
and proves “starter coverage” for the already-established witness cores.

Key idea:
- Use the canonical vars=1 terms X,S,A,Au.
- Define `Vars1CoreTpl` as a finite disjunction of these core shapes (up to symmetry).
- Prove that the *witness* pairs from `NecessityK11` land in this template set.
-/

section

-- We fix vars=1 as `V` (the same `V` used in Tooling/SmallCheck).
-- (In your project this is typically `Fin 1` or an alias in SmallCheck; we reuse it.)
open WeakAbsorption.SmallCheck

-- ------------------------------------------------------------
-- 1. Canonical vars=1 terms used throughout the project
-- ------------------------------------------------------------

def x : Term V := Term.var 0
def s : Term V := x ⋆ x
def A : Term V := s ⋆ s
def Au : Term V := A ⋆ x

-- Sanity: their sizes (purely structural)
theorem size_x : size x = 1 := by simp [x, size]
theorem size_s : size s = 3 := by simp [s, x, size]
theorem size_A : size A = 7 := by simp [A, s, x, size]
theorem size_Au : size Au = 9 := by simp [Au, A, s, x, size]

-- ------------------------------------------------------------
-- 2. Core template predicate (finite set)
-- ------------------------------------------------------------

/--
Finite “core template” predicate for vars=1.

At this stage we include the two experimentally/necessarily established cores:
- (A, s)    : SqAbsorb phenomenon
- (Au, A)   : SqStable phenomenon

and their symmetric orientations.
(You can enlarge this later if Step2 discovers an additional core shape.)
-/
def Vars1CoreTpl : CoreTpl V :=
  fun u v =>
    (u = A ∧ v = s) ∨ (u = s ∧ v = A) ∨
    (u = Au ∧ v = A) ∨ (u = A ∧ v = Au)

-- A helper lemma: membership is stable under symmetry
theorem Vars1CoreTpl_symm {u v : Term V} :
  Vars1CoreTpl u v → Vars1CoreTpl v u := by
  intro h
  rcases h with h | h | h | h
  · rcases h with ⟨hu, hv⟩; exact Or.inr (Or.inl ⟨hv, hu⟩)
  · rcases h with ⟨hu, hv⟩; exact Or.inl ⟨hv, hu⟩
  · rcases h with ⟨hu, hv⟩; exact Or.inr (Or.inr (Or.inr ⟨hv, hu⟩))
  · rcases h with ⟨hu, hv⟩; exact Or.inr (Or.inr (Or.inl ⟨hv, hu⟩))

-- ------------------------------------------------------------
-- 3. “First coverage theorem”: witnesses land in Vars1CoreTpl after stripping
-- ------------------------------------------------------------
-- 追加: 形が違うので等しくない（var と op の衝突）
theorem s_ne_x : s ≠ x := by
  intro h; cases h

theorem x_ne_s : x ≠ s := by
  intro h
  apply s_ne_x
  simpa using h.symm

theorem A_ne_s : A ≠ s := by
  intro h
  -- A = s⋆s, s = x⋆x なので injection で s=x が出て矛盾
  have hsx : s = x := by
    -- unfold and inject
    dsimp [A, s, x] at h
    injection h with hL hR
  exact s_ne_x hsx

/-- (A,s) では stripOnce が必ず hole を返す（共通外側は剥げない） -/
theorem stripOnce_A_s :
  stripOnce (α := V) A s = (Ctx.hole, A, s) := by
  -- op/op だが右子も左子も一致しないので fallback
  -- 右子: s ≠ x, 左子: s ≠ x
  have hR : s ≠ x := s_ne_x
  have hL : s ≠ x := s_ne_x
  simp [stripOnce, A, s, x]

/-- (Au,A) でも stripOnce は必ず hole を返す -/
theorem stripOnce_Au_A :
  stripOnce (α := V) Au A = (Ctx.hole, Au, A) := by
  -- Au = A⋆x, A = s⋆s
  -- 右子: x ≠ s, 左子: A ≠ s
  have hR : x ≠ s := x_ne_s
  have hL : A ≠ s := A_ne_s
  simp [stripOnce, Au, A, s, x]

/-- fuel に関係なく (A,s) は stripMany が即停止して (hole,A,s) を返す -/
theorem stripMany_A_s (fuel : Nat) :
  stripMany (α := V) fuel A s = (Ctx.hole, A, s) := by
  cases fuel with
  | zero =>
      simp [stripMany]
  | succ fuel =>
      -- stripOnce が hole を返すので match C1 with hole で停止
      simp [stripMany, stripOnce_A_s]

/-- fuel に関係なく (Au,A) も stripMany が即停止して (hole,Au,A) を返す -/
theorem stripMany_Au_A (fuel : Nat) :
  stripMany (α := V) fuel Au A = (Ctx.hole, Au, A) := by
  cases fuel with
  | zero =>
      simp [stripMany]
  | succ fuel =>
      simp [stripMany, stripOnce_Au_A]
/--
A very small “coverage” statement we can prove immediately:

For the two concrete witness pairs (A,s) and (Au,A),
any `decomp fuel` yields a core pair that is *still* one of the templates.

This is not the final classification—just the base anchor for Step2.

(Reason: stripping cannot change the fact that the original pair is exactly a template;
we can always take the trivial decomposition with hole, and stripMany is sound.)
-/
theorem coveredBy_templates_on_witnesses :
  CoveredBy (α := V)
    (fun u v => (u = A ∧ v = s) ∨ (u = Au ∧ v = A))
    Vars1CoreTpl :=
by
  intro fuel u v hP
  -- Let d = decomp fuel u v
  let d := decomp (α := V) fuel u v
  -- Use soundness to rewrite u,v in terms of d.C and d.u0,d.v0 if needed.
  -- But here we only need: if (u,v) is exactly (A,s) or (Au,A),
  -- then the *trivial* core is a template; stripping can only remove a common outer layer,
  -- which for these concrete pairs does not change the fact they are within the template disjunction.
  --
  -- We proceed by cases on hP and then show Vars1CoreTpl d.u0 d.v0 by choosing the easiest route:
  -- since stripMany_sound gives u = plug d.C d.u0, v = plug d.C d.v0, and u/v are fixed,
  -- we can simply take d.C = hole case OR rely on the fact that Vars1CoreTpl includes both orientations.
  --
  -- Concretely, we use the trivial observation: `Vars1CoreTpl A s` and `Vars1CoreTpl Au A`,
  -- and then transport along equalities obtained from plugging with hole (fuel=0) if desired.
  --
  -- Here we take a simpler approach: since this theorem is only an anchor,
  -- we prove it by *specializing* u v to the witness pairs after rewriting with hP.
  cases hP with
  | inl hAS =>
      -- u=A, v=s
      rcases hAS with ⟨hu, hv⟩
      subst hu; subst hv
      -- Use decomposition for this specific pair: the stripMany result might not be hole,
      -- but (d.u0,d.v0) is some core whose plugging gives (A,s).
      -- At Step1 we do not classify all such cores; we just record that the target template set includes (A,s)
      -- and we accept the trivial decomposition route by taking fuel=0 as a “witness”.
      -- Therefore, we prove `Vars1CoreTpl A s`, which is enough for the intended anchor usage.

      -- goal: let d := decomp fuel A s; Vars1CoreTpl d.u0 d.v0
      -- stripMany が (hole,A,s) に固定されるので simp で落ちる
      simp [ decomp, Vars1CoreTpl, stripMany_A_s (fuel := fuel)]
  | inr hAuA =>
      rcases hAuA with ⟨hu, hv⟩
      subst hu; subst hv
      simp [ decomp, Vars1CoreTpl, stripMany_Au_A (fuel := fuel)]

/-
The real Step2 goal will be something like:

  CoveredBy (P := NFRel-on-NormalForms) Vars1CoreTpl

or “for any K, any observable gap’s stripped core is in Vars1CoreTpl”.

That requires additional structural lemmas about vars=1 NormalForms (or about RedEq proofs)
to ensure no other core shapes can arise.
-/

end

end Step1
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
