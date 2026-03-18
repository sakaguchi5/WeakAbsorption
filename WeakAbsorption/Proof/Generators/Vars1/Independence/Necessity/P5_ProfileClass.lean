import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareProfileClass
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_ObstructionProfile

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5_has_rightLeftRightMidProfile {α : Type} (x p z : Term α) :
    RightLeftRightMidProfile (P5_mediumSquareBoundary x p z) := by
  exact P5_mediumSquareBoundary_profile x p z

theorem P5_profileClass_summary {α : Type} (x p z : Term α) :
    (∃ L : Term α, squareTerm L = P5Term x p z ∧
        ∀ {t u : Term α}, t.op u = P5Term x p z ↔ t = L ∧ u = L) ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) ∧
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqAbsorb_shape =
      SelfEmbeddingShape.rightNest ∧
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqStable_shape =
      SelfEmbeddingShape.leftNest ∧
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).decor_shape =
      SelfEmbeddingShape.rightNest ∧
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).c2c1_shape =
      SelfEmbeddingShape.midNest := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨P5Core x p z, P5Core_squareTerm_eq_P5Term x p z, ?_⟩
    intro t u
    constructor
    · intro hEq
      exact P5_boundary_root_rigid (x := x) (p := p) (z := z) hEq
    · rintro ⟨rfl, rfl⟩
      exact (P5Core_squareTerm_eq_P5Term x p z).symm
  · exact P5_not_primitiveR4RootSeed x p z
  · exact P5_sqAbsorb_obstruction_shape x p z
  · exact P5_sqStable_obstruction_shape x p z
  · exact P5_decor_obstruction_shape x p z
  · exact P5_c2c1_obstruction_shape x p z

theorem P5_profileClass_square_outsider {α : Type} (x p z : Term α) :
    (∃ L : Term α, squareTerm L = P5Term x p z) ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  refine ⟨?_, P5_not_primitiveR4RootSeed x p z⟩
  exact ⟨P5Core x p z, P5Core_squareTerm_eq_P5Term x p z⟩

theorem P5_profileClass_boundary_witness {α : Type} (x p z : Term α) :
    ∃ B : MediumSquareBoundary α,
      RightLeftRightMidProfile B ∧
      B.term = P5Term x p z := by
  refine ⟨P5_mediumSquareBoundary x p z, ?_, ?_⟩
  · exact P5_has_rightLeftRightMidProfile x p z
  · exact P5_mediumSquareBoundary_term x p z

theorem P5_profileClass_generic_outsider {α : Type} (x p z : Term α) :
    (∃ L : Term α, squareTerm L = P5Term x p z) ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  exact rightLeftRightMidProfile_square_outsider
    (P5_profileClass_boundary_witness x p z)

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
