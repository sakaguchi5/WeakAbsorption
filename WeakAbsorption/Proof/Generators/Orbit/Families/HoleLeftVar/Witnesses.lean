import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure

import WeakAbsorption.Proof.Generators.Orbit.Families.HoleLeftVar.Defs
import WeakAbsorption.Proof.Generators.Orbit.KDynamics

namespace WeakAbsorption
namespace WAA
namespace OrbitSafeHoleLeftVar
namespace Witnesses

open WeakAbsorption.WAA.OrbitKDynamics

section
variable {α : Type} (a : α)

-- ------------------------------------------------------------
-- Concrete vars=1-style witnesses (same shapes as SmallCheck)
-- ------------------------------------------------------------

def X : Term α := Term.var a
def S : Term α := (X (a := a)) ⋆ (X (a := a))
def A : Term α := (S (a := a)) ⋆ (S (a := a))
def Au : Term α := (A (a := a)) ⋆ (X (a := a))

-- ------------------------------------------------------------
-- Normality (local, minimal)
-- ------------------------------------------------------------

theorem X_normal : Normal (α := α) (X (a := a)) := by
  intro u hu
  cases hu with
  | step _ _ hs => cases hs

theorem not_C1_X_X : ¬ IsC1Root (α := α) (X (a := a)) (X (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  cases hw

theorem not_C2_X_X : ¬ IsC2pRoot (α := α) (X (a := a)) (X (a := a)) := by
  simp [IsC2pRoot, X]

theorem S_normal : Normal (α := α) (S (a := a)) := by
  -- Normal_op_iff : Normal (t⋆u) ↔ Normal t ∧ Normal u ∧ ¬IsC1Root t u ∧ ¬IsC2pRoot t u
  exact (Normal_op_iff (α := α) (X (a := a)) (X (a := a))).2
    ⟨X_normal (a := a), X_normal (a := a), not_C1_X_X (a := a), not_C2_X_X (a := a)⟩

theorem not_C1_S_S : ¬ IsC1Root (α := α) (S (a := a)) (S (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  -- (x⋆x) = w⋆(x⋆x) ⇒ right child mismatch forces a contradiction
  dsimp [S, X] at hw
  injection hw with hL hR
  -- hL : (var a) = w  (ok) ; hR : (var a) = (var a ⋆ var a) impossible
  cases hR

theorem not_C2_S_S : ¬ IsC2pRoot (α := α) (S (a := a)) (S (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  dsimp [IsC2pRoot, S, X] at hw
  -- (x⋆x) = ((w⋆x)⋆x) ⇒ left child mismatch gives var = op
  injection hw with h1 h2
  cases h1

theorem A_normal : Normal (α := α) (A (a := a)) := by
  exact (Normal_op_iff (α := α) (S (a := a)) (S (a := a))).2
    ⟨S_normal (a := a), S_normal (a := a), not_C1_S_S (a := a), not_C2_S_S (a := a)⟩

theorem not_C1_A_X : ¬ IsC1Root (α := α) (A (a := a)) (X (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  -- A = w⋆x ⇒ right child forces S = x (impossible)
  dsimp [A, S, X] at hw
  injection hw with _ hR
  cases hR

theorem Au_normal : Normal (α := α) (Au (a := a)) := by
  -- right operand is var, so C2p cannot fire; C1 cannot fire because A is not a _⋆x form
  exact (Normal_op_iff (α := α) (A (a := a)) (X (a := a))).2
    ⟨A_normal (a := a),
      X_normal (a := a),
      not_C1_A_X (a := a),
      not_IsC2pRoot_rightVar (α := α) a (A (a := a))⟩

-- ------------------------------------------------------------
-- Domain facts for □⋆x : DomNoC1 a t := ¬ IsC1Root t (var a)
-- ------------------------------------------------------------

/-- S = x⋆x IS a C1-root against x, so □⋆x is NOT safe on S. -/
theorem not_DomNoC1_S : ¬ DomNoC1 (α := α) a (S (a := a)) := by
  intro h
  -- show IsC1Root S x by witness x
  apply h
  refine ⟨X (a := a), ?_⟩
  simp [S, X]

/-- A = (x⋆x)⋆(x⋆x) is NOT a C1-root against x, so □⋆x is safe on A. -/
theorem DomNoC1_A : DomNoC1 (α := α) a (A (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  dsimp [A, S, X] at hw
  injection hw with _ hR
  -- hR : (x⋆x) = x impossible
  cases hR

/-- Au = A⋆x IS a C1-root against x, so □⋆x is NOT safe on Au. -/
theorem not_DomNoC1_Au : ¬ DomNoC1 (α := α) a (Au (a := a)) := by
  intro h
  apply h
  refine ⟨A (a := a), ?_⟩
  simp [Au, X]

-- ------------------------------------------------------------
-- Consequences: □⋆x preserves Normal exactly on the “domain” we want
-- ------------------------------------------------------------

/-- Plugging A into □⋆x stays Normal (this is the *good* case). -/
theorem plug_holeLeftVar_A_normal :
  Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) (A (a := a))) := by
  exact normal_plug_holeLeftVar (α := α) a
    (t := A (a := a))
    (A_normal (a := a))
    (DomNoC1_A (a := a))

/-- Plugging S into □⋆x is NOT Normal (C1 fires immediately). -/
theorem not_normal_plug_holeLeftVar_S :
  ¬ Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) (S (a := a))) := by
  intro hn
  -- plug = S ⋆ x
  have hn' : Normal (α := α) ((S (a := a)) ⋆ (X (a := a))) := by
    simpa [holeLeftVar, Ctx.plug, S, X] using hn
  rcases (Normal_op_iff (α := α) (S (a := a)) (X (a := a))).1 hn' with ⟨_,_,hnoC1,_⟩
  -- but IsC1Root S x holds
  have hC1 : IsC1Root (α := α) (S (a := a)) (X (a := a)) := by
    refine ⟨X (a := a), ?_⟩
    simp [S, X]
  exact hnoC1 hC1

/-- Plugging Au into □⋆x is NOT Normal (C1 fires immediately). -/
theorem not_normal_plug_holeLeftVar_Au :
  ¬ Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) (Au (a := a))) := by
  intro hn
  have hn' : Normal (α := α) ((Au (a := a)) ⋆ (X (a := a))) := by
    simpa [holeLeftVar, Ctx.plug, Au, X] using hn
  rcases (Normal_op_iff (α := α) (Au (a := a)) (X (a := a))).1 hn' with ⟨_,_,hnoC1,_⟩
  have hC1 : IsC1Root (α := α) (Au (a := a)) (X (a := a)) := by
    refine ⟨A (a := a), ?_⟩
    simp [Au, X]
  exact hnoC1 hC1

-- ------------------------------------------------------------
-- Optional: connect to K-dynamics (size only, independent of Normality)
-- ------------------------------------------------------------

theorem size_X : size (X (a := a)) = 1 := by simp [X, size]
theorem size_S : size (S (a := a)) = 3 := by simp [S, X, size]
theorem size_A : size (A (a := a)) = 7 := by simp [A, S, X, size]
theorem size_Au : size (Au (a := a)) = 9 := by simp [Au, A, S, X, size]

/-- Size-wise, □⋆x has offset 2, so A fits into K=11 after plugging (7+2 ≤ 11). -/
theorem visible_K11_holeLeftVar_A :
  VisibleAt (α := α) 11 (holeLeftVar (α := α) a) (A (a := a)) := by
  -- size A + offset 2 ≤ 11
  have : size (A (a := a)) + Ctx.sizeOffset (α := α) (holeLeftVar (α := α) a) ≤ 11 := by
    simp [size_A (a := a), sizeOffset_holeLeftVar (α := α) a]
  exact (visibleAt_iff (α := α) (K := 11) (D := holeLeftVar (α := α) a) (t := A (a := a))).2 this

end

end Witnesses
end OrbitSafeHoleLeftVar
end WAA
end WeakAbsorption
