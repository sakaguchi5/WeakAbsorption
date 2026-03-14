import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Equational
import WeakAbsorption.Core.Measure

import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Spec.Rule

/-!
# Necessity at K=11 (vars = 1 witness terms)

This file turns the K=11 SmallCheck "discovery order" into *proof-side propositions*
by providing explicit NormalForm witnesses:

1) SqAbsorb is necessary:
   There exist distinct normal forms x ≠ y with NFRel x y but ¬ NFEqR [] x y.

2) SqStable is necessary after SqAbsorb:
   There exist normal forms x,y with NFRel x y but ¬ NFEqR [SqAbsorb] x y,
   witnessed by A ~ A⋆x (the "SqStable phenomenon").

No Tooling/SmallCheck is imported; we only use Proof/Generators definitions.
-/

open WeakAbsorption.Closure
open WeakAbsorption.Spec

namespace WeakAbsorption
namespace WAA
namespace NecessityK11

section
variable {α : Type} (a : α)

-- ------------------------------------------------------------
-- Concrete vars=1 terms (same shapes as the SmallCheck logs)
-- ------------------------------------------------------------

private def X : Term α := Term.var a               -- x
private def S : Term α := (X (a := a)) ⋆ (X (a := a))     -- x⋆x
private def A : Term α := (S (a := a)) ⋆ (S (a := a))     -- (x⋆x)⋆(x⋆x)
private def Au : Term α := (A (a := a)) ⋆ (X (a := a))    -- ((x⋆x)⋆(x⋆x))⋆x

-- ------------------------------------------------------------
-- Normality of the concrete terms
-- ------------------------------------------------------------

private theorem X_normal : Normal (X (a := a)) := by
  intro u hu
  cases hu with
  | step _ _ hs => cases hs

private theorem not_C1_X_X :
  ¬ IsC1Root (α := α) (X (a := a)) (X (a := a)) := by
  rintro ⟨w, hw⟩
  -- var = op ...
  cases hw

private theorem not_C2_X_X :
  ¬ IsC2pRoot (α := α) (X (a := a)) (X (a := a)) := by
  -- u is a var, so IsC2pRoot is False by definition
  simp [IsC2pRoot, X]

private theorem S_normal : Normal (S (a := a)) := by
  -- Normal_op_iff : Normal (t⋆u) ↔ Normal t ∧ Normal u ∧ ¬IsC1Root t u ∧ ¬IsC2pRoot t u
  exact (Normal_op_iff (α := α) (X (a := a)) (X (a := a))).2
    ⟨X_normal (a := a), X_normal (a := a), not_C1_X_X (a := a), not_C2_X_X (a := a)⟩

private theorem not_C1_S_S :
  ¬ IsC1Root (α := α) (S (a := a)) (S (a := a)) := by
  rintro ⟨w, hw⟩
  dsimp [S, X] at hw
  -- hw : (var a ⋆ var a) = (w ⋆ (var a ⋆ var a))
  injection hw with hL hR
  -- hL : var a = w
  -- hR : var a = var a ⋆ var a
  cases hR

private theorem not_C2_S_S :
  ¬ IsC2pRoot (α := α) (S (a := a)) (S (a := a)) := by
  -- Here u = S is an op, so IsC2pRoot asks S = ((w⋆y)⋆z) for u = (y⋆z).
  -- But S has only depth 1 at the root, so impossible.
  dsimp [IsC2pRoot, S, X]
  rintro ⟨w, hw⟩
  -- hw : (x⋆x) = ((w⋆x)⋆x)
  injection hw with h1 h2
  -- h1 : x = (w⋆x) (var = op)
  cases h1

private theorem A_normal : Normal (A (a := a)) := by
  exact (Normal_op_iff (α := α) (S (a := a)) (S (a := a))).2
    ⟨S_normal (a := a), S_normal (a := a), not_C1_S_S (a := a), not_C2_S_S (a := a)⟩

private theorem not_C1_A_X :
  ¬ IsC1Root (α := α) (A (a := a)) (X (a := a)) := by
  rintro ⟨w, hw⟩
  dsimp [A, S, X] at hw
  -- (S⋆S) = w⋆x ⇒ right child mismatch (op vs var)
  injection hw with _ hR
  -- hR : S = x
  cases hR

private theorem not_C2_A_X :
  ¬ IsC2pRoot (α := α) (A (a := a)) (X (a := a)) := by
  simp [IsC2pRoot, X]

private theorem Au_normal : Normal (Au (a := a)) := by
  exact (Normal_op_iff (α := α) (A (a := a)) (X (a := a))).2
    ⟨A_normal (a := a), X_normal (a := a), not_C1_A_X (a := a), not_C2_A_X (a := a)⟩

-- Package into NormalForm witnesses
private def nfS : NormalForm α := ⟨S (a := a), S_normal (a := a)⟩
private def nfA : NormalForm α := ⟨A (a := a), A_normal (a := a)⟩
private def nfAu : NormalForm α := ⟨Au (a := a), Au_normal (a := a)⟩

-- ------------------------------------------------------------
-- Size bounds (connects to "K=11" witness property)
-- ------------------------------------------------------------

private theorem size_S : size (S (a := a)) = 3 := by
  simp [size, S, X]

private theorem size_A : size (A (a := a)) = 7 := by
  simp [size, A, S, X]

private theorem size_Au : size (Au (a := a)) = 9 := by
  simp [size, Au, A, S, X]

private theorem size_S_le_11 : size (S (a := a)) ≤ 11 := by
  simp [size_S (a := a)]

private theorem size_A_le_11 : size (A (a := a)) ≤ 11 := by
  simp [size_A (a := a)]

private theorem size_Au_le_11 : size (Au (a := a)) ≤ 11 := by
  simp [size_Au (a := a)]

-- ------------------------------------------------------------
-- NFRel witnesses (true in the full theory)
-- ------------------------------------------------------------

/-- A ~ S in NFRel (this is the SqAbsorb phenomenon at term-level). -/
private theorem NFRel_A_S : NFRel (α := α) (nfA (a := a)) (nfS (a := a)) := by
  -- NFRel x y := RedEq x.1 y.1
  dsimp [NFRel, nfA, nfS]
  -- use the already proved term-level lemma from NormalFormGenerators
  simpa [A, S, X] using (RedEq_absorb_sq_right (α := α) (t := X (a := a)) (u := X (a := a)))

/-- Au ~ A in NFRel (this is the SqStable phenomenon at term-level). -/
private theorem NFRel_Au_A : NFRel (α := α) (nfAu (a := a)) (nfA (a := a)) := by
  dsimp [NFRel, nfAu, nfA]
  simpa [Au, A, S, X] using (RedEq_sq_right_stable (α := α) (t := X (a := a)) (u := X (a := a)))

-- ------------------------------------------------------------
-- (1) SqAbsorb necessity: with no generators, NFEqR [] collapses to equality.
-- ------------------------------------------------------------

theorem NFEqR_nil_eq {x y : NormalForm α} :
  NFEqR (α := α) ([] : RuleSet) x y → x = y := by
  intro h
  -- NFEqR R := EqvGen (NFStepR R)
  induction h with
  | rel a b hab =>
      rcases hab with ⟨tag, hin, _⟩
      -- tag ∈ [] is impossible
      cases hin
  | refl a =>
      rfl
  | symm a b _ ih =>
      exact ih.symm
  | trans a b c _ _ ih1 ih2 =>
      exact ih1.trans ih2

theorem sqAbsorb_is_necessary_K11 (a : α) :
  ∃ x y : NormalForm α,
    x ≠ y ∧
    size x.1 ≤ 11 ∧ size y.1 ≤ 11 ∧
    NFRel (α := α) x y ∧
    ¬ NFEqR (α := α) ([] : RuleSet) x y :=
by
  let x := nfA (a := a)
  let y := nfS (a := a)
  -- 先に x ≠ y の証明を定義して重複を避ける
  have hne : x ≠ y := by
    intro h
    -- reduce to term inequality
    have : (A (a := a)) = (S (a := a)) := congrArg Subtype.val h
    -- op = op; but sizes differ, easiest:
    have hs : size (A (a := a)) = size (S (a := a)) := by simp [this]
    -- contradiction using computed sizes
    simp [size_A (a := a), size_S (a := a)] at hs

  refine ⟨x, y, hne, ?_, ?_, ?_, ?_⟩
  · exact size_A_le_11 (a := a)
  · exact size_S_le_11 (a := a)
  · exact NFRel_A_S (a := a)
  · intro h
    have hxy := NFEqR_nil_eq (α := α) (x := x) (y := y) h
    exact hne hxy

-- ------------------------------------------------------------
-- (2) SqStable necessity after SqAbsorb:
--     Under SqAbsorb-only, a simple invariant (leaf parity) separates A and Au.
-- ------------------------------------------------------------

/-- Leaf parity (= leafCount mod 2) computed structurally (no Nat arithmetic). -/
def leafParity {α : Type} : Term α → Bool
  | .var _  => true
  | .op t u => Bool.xor (leafParity t) (leafParity u)

private theorem leafParity_sqAbsorb_inner (t u : Term α) :
  leafParity ((t ⋆ u) ⋆ (u ⋆ u)) = leafParity (t ⋆ u) := by
  simp [leafParity,Bool.xor_comm]

private theorem Ctx_leafParity_congr (C : Ctx α) {t u : Term α} :
  leafParity t = leafParity u →
  leafParity (Ctx.plug C t) = leafParity (Ctx.plug C u) := by
  intro h
  induction C with
  | hole =>
      -- plug hole t = t なので、前提 h そのもの
      simpa [Ctx.plug] using h
  | left C r ih =>
      -- ih の型はすでに leafParity (Ctx.plug C t) = leafParity (Ctx.plug C u)
      simp [Ctx.plug, leafParity, ih]
  | right l C ih =>
      -- node l (plug C t) のパリティは (leafParity l) XOR (leafParity (plug C t))
      -- ih によって (leafParity (plug C t)) 部分の等価性が示されています
      simp [Ctx.plug, leafParity, ih]

private theorem NFSqStepCtx_preserves_leafParity {x y : NormalForm α} :
  NFSqStepCtx (α := α) x y → leafParity x.1 = leafParity y.1 := by
  rintro ⟨C, t, u, hx, hy⟩
  -- x.1 と y.1 を、コンテキストの形に書き換える
  rw [hx, hy]
  -- あとはコンテキストの合同性定理を適用するだけ
  exact Ctx_leafParity_congr C (leafParity_sqAbsorb_inner t u)

private theorem NFStepR_sqAbsorb_preserves_leafParity {x y : NormalForm α} :
  NFStepR (α := α) ([RuleId.SqAbsorb] : RuleSet) x y →
  leafParity x.1 = leafParity y.1 := by
  rintro ⟨tag, hin, hstep⟩
  have ht : tag = RuleId.SqAbsorb := by
    simpa using hin
  subst ht
  -- step SqAbsorb = NFSqStepCtx
  exact NFSqStepCtx_preserves_leafParity (α := α) hstep

theorem NFEqR_sqAbsorb_preserves_leafParity {x y : NormalForm α} :
  NFEqR (α := α) ([RuleId.SqAbsorb] : RuleSet) x y →
  leafParity x.1 = leafParity y.1 := by
  intro h
  induction h with
  | rel a b hab =>
      exact NFStepR_sqAbsorb_preserves_leafParity (α := α) hab
  | refl a =>
      rfl
  | symm a b _ ih =>
      exact ih.symm
  | trans a b c _ _ ih1 ih2 =>
      exact ih1.trans ih2

private theorem leafParity_A :
  leafParity (A (a := a)) = false := by
  simp [A, S, X, leafParity]

private theorem leafParity_Au :
  leafParity (Au (a := a)) = true := by
  simp [Au, A, S, X, leafParity]

theorem sqStable_is_necessary_after_sqAbsorb_K11 (a : α) :
  ∃ x y : NormalForm α,
    size x.1 ≤ 11 ∧ size y.1 ≤ 11 ∧
    NFRel (α := α) x y ∧
    ¬ NFEqR (α := α) ([RuleId.SqAbsorb] : RuleSet) x y :=
by
  -- Use x = Au, y = A (both normal), since NFRel(Au,A) holds but SqAbsorb-only can't change leafParity.
  refine ⟨nfAu (a := a), nfA (a := a), ?_, ?_, ?_, ?_⟩
  · exact size_Au_le_11 (a := a)
  · exact size_A_le_11 (a := a)
  · exact NFRel_Au_A (a := a)
  · intro h
    have hpar := NFEqR_sqAbsorb_preserves_leafParity (α := α) (x := nfAu (a := a)) (y := nfA (a := a)) h
    -- contradict parity values
    have : leafParity (Au (a := a)) = leafParity (A (a := a)) := by
      simpa [nfAu, nfA] using hpar
    -- Au parity = true, A parity = false
    simp [leafParity_A (a := a), leafParity_Au (a := a)] at this

end

end NecessityK11
end WAA
end WeakAbsorption
