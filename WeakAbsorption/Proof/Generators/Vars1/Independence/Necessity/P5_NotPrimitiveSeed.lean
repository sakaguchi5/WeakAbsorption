import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareNotPrimitive
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_MediumReduction

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5_not_primitiveR4RootSeed {α : Type} (x p z : Term α) :
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  exact mediumSquareBoundary_not_primitiveR4RootSeed (P5_isMediumSquareBoundary x p z)

theorem P5_reclassified {α : Type} (x p z : Term α) :
    ∃ L : Term α, squareTerm L = P5Term x p z ∧ ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  exact mediumSquareBoundary_reclassified (P5_isMediumSquareBoundary x p z)

theorem P5_reclassified_canonical {α : Type} (x p z : Term α) :
    squareTerm (P5Core x p z) = P5Term x p z ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  refine ⟨P5Core_squareTerm_eq_P5Term x p z, ?_⟩
  exact P5_not_primitiveR4RootSeed x p z

theorem P5_square_outsider {α : Type} (x p z : Term α) :
    (∃ L : Term α, squareTerm L = P5Term x p z) ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  exact mediumSquareBoundary_square_outsider (P5_isMediumSquareBoundary x p z)

theorem P5_square_outsider_with_profile {α : Type} (x p z : Term α) :
    ((∃ L : Term α, squareTerm L = P5Term x p z) ∧
      ¬ IsPrimitiveR4RootSeed (P5Term x p z))
    ∧
    (P5_mediumSquareBoundary x p z).profile =
      ( SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.leftNest
      , SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.midNest ) := by
  refine ⟨P5_square_outsider x p z, ?_⟩
  exact P5_mediumSquareBoundary_profile x p z

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
