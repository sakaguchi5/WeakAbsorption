import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareBoundary
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_MediumBoundary

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/-- `P5` as a formal medium square boundary object. -/
def P5_mediumSquareBoundary {α : Type} (x p z : Term α) : MediumSquareBoundary α :=
  { core := P5Core x p z
    admissible := P5Core_mediumSquareAdmissible x p z }

theorem P5_mediumSquareBoundary_term {α : Type} (x p z : Term α) :
    (P5_mediumSquareBoundary x p z).term = P5Term x p z := by
  exact P5Core_squareTerm_eq_P5Term x p z

theorem P5_mediumSquareBoundary_profile {α : Type} (x p z : Term α) :
    (P5_mediumSquareBoundary x p z).profile =
      ( SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.leftNest
      , SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.midNest ) := by
  -- 定義を展開
  simp [P5_mediumSquareBoundary, MediumSquareBoundary.profile, MediumSquareAdmissible.profile]
  repeat constructor -- ∧ をバラバラにする
  all_goals rfl      -- 残ったすべての等式に rfl を適用

theorem P5_isMediumSquareBoundary {α : Type} (x p z : Term α) :
    IsMediumSquareBoundary (P5Term x p z) := by
  refine ⟨P5_mediumSquareBoundary x p z, ?_⟩
  exact P5_mediumSquareBoundary_term x p z

theorem P5_boundary_root_rigid {α : Type} (x p z : Term α)
    {t u : Term α} (h : t.op u = P5Term x p z) :
    t = P5Core x p z ∧ u = P5Core x p z := by
  rw [← P5_mediumSquareBoundary_term (x := x) (p := p) (z := z)] at h
  exact (P5_mediumSquareBoundary x p z).root_rigid h

theorem P5_boundary_children_equal {α : Type} (x p z : Term α)
    {t u : Term α} (h : t.op u = P5Term x p z) :
    t = u := by
  rw [← P5_mediumSquareBoundary_term (x := x) (p := p) (z := z)] at h
  exact (P5_mediumSquareBoundary x p z).children_equal h

theorem P5_boundary_object_summary {α : Type} (x p z : Term α) :
    IsMediumSquareBoundary (P5Term x p z) ∧
    (P5_mediumSquareBoundary x p z).profile =
      ( SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.leftNest
      , SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.midNest ) := by
  refine ⟨P5_isMediumSquareBoundary x p z, ?_⟩
  exact P5_mediumSquareBoundary_profile x p z

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
