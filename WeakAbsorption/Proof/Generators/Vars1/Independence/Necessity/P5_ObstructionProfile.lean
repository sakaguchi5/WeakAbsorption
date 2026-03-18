import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_NotPrimitiveSeed

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5_sqAbsorb_obstruction_shape {α : Type} (x p z : Term α) :
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqAbsorb_shape =
      SelfEmbeddingShape.rightNest := by
  rfl

theorem P5_sqStable_obstruction_shape {α : Type} (x p z : Term α) :
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqStable_shape =
      SelfEmbeddingShape.leftNest := by
  rfl

theorem P5_decor_obstruction_shape {α : Type} (x p z : Term α) :
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).decor_shape =
      SelfEmbeddingShape.rightNest := by
  rfl

theorem P5_c2c1_obstruction_shape {α : Type} (x p z : Term α) :
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).c2c1_shape =
      SelfEmbeddingShape.midNest := by
  rfl

theorem P5_obstruction_profile_expanded {α : Type} (x p z : Term α) :
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqAbsorb_shape =
        SelfEmbeddingShape.rightNest) ∧
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqStable_shape =
        SelfEmbeddingShape.leftNest) ∧
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).decor_shape =
        SelfEmbeddingShape.rightNest) ∧
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).c2c1_shape =
        SelfEmbeddingShape.midNest) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact P5_sqAbsorb_obstruction_shape x p z
  · exact P5_sqStable_obstruction_shape x p z
  · exact P5_decor_obstruction_shape x p z
  · exact P5_c2c1_obstruction_shape x p z

theorem P5_boundary_profile_named {α : Type} (x p z : Term α) :
    (P5_mediumSquareBoundary x p z).profile =
      ( SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.leftNest
      , SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.midNest ) := by
  exact P5_mediumSquareBoundary_profile x p z

theorem P5_boundary_object_certified {α : Type} (x p z : Term α) :
    ∃ B : MediumSquareBoundary α,
      B.term = P5Term x p z ∧
      B.profile =
        ( SelfEmbeddingShape.rightNest
        , SelfEmbeddingShape.leftNest
        , SelfEmbeddingShape.rightNest
        , SelfEmbeddingShape.midNest ) := by
  refine ⟨P5_mediumSquareBoundary x p z, ?_⟩
  refine ⟨?_, ?_⟩
  · exact P5_mediumSquareBoundary_term x p z
  · exact P5_mediumSquareBoundary_profile x p z

theorem P5_square_outsider_named {α : Type} (x p z : Term α) :
    (squareTerm (P5Core x p z) = P5Term x p z) ∧
    (¬ IsPrimitiveR4RootSeed (P5Term x p z)) ∧
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqAbsorb_shape =
        SelfEmbeddingShape.rightNest) ∧
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).sqStable_shape =
        SelfEmbeddingShape.leftNest) ∧
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).decor_shape =
        SelfEmbeddingShape.rightNest) ∧
    ((P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).c2c1_shape =
        SelfEmbeddingShape.midNest) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P5Core_squareTerm_eq_P5Term x p z
  · exact P5_not_primitiveR4RootSeed x p z
  · exact P5_sqAbsorb_obstruction_shape x p z
  · exact P5_sqStable_obstruction_shape x p z
  · exact P5_decor_obstruction_shape x p z
  · exact P5_c2c1_obstruction_shape x p z

theorem P5_medium_boundary_object_summary {α : Type} (x p z : Term α) :
    IsMediumSquareBoundary (P5Term x p z) ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) ∧
    ∃ B : MediumSquareBoundary α,
      B.term = P5Term x p z ∧
      B.profile =
        ( SelfEmbeddingShape.rightNest
        , SelfEmbeddingShape.leftNest
        , SelfEmbeddingShape.rightNest
        , SelfEmbeddingShape.midNest ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact P5_isMediumSquareBoundary x p z
  · exact P5_not_primitiveR4RootSeed x p z
  · exact P5_boundary_object_certified x p z

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
