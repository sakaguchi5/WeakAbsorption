import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_Status
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_MediumSquareAdmissible

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5_medium_square_status {α : Type} (x p z : Term α) :
    IsMediumSquareAdmissible (P5Core x p z) := by
  exact P5Core_isMediumSquareAdmissible x p z

theorem P5_medium_profile_witness {α : Type} (x p z : Term α) :
    ∃ h : MediumSquareAdmissible (P5Core x p z),
      h.profile =
        ( SelfEmbeddingShape.rightNest
        , SelfEmbeddingShape.leftNest
        , SelfEmbeddingShape.rightNest
        , SelfEmbeddingShape.midNest ) := by
  refine ⟨P5Core_mediumSquareAdmissible x p z, ?_⟩
  simpa using P5Core_medium_profile x p z

theorem P5_medium_boundary {α : Type} (x p z : Term α) :
    ((NoRootInstance sqAbsorbPat (P5Term x p z) ∧
      NoRootInstance sqStablePat (P5Term x p z) ∧
      NoRootInstance decorPat (P5Term x p z) ∧
      NoRootInstance c2c1Pat (P5Term x p z))
     ∧
     (squareTerm (P5Core x p z) = P5Term x p z))
    ∧
    IsMediumSquareAdmissible (P5Core x p z) := by
  refine ⟨?_, P5Core_isMediumSquareAdmissible x p z⟩
  refine ⟨P5_root_excluded_from_R4_patterns x p z, ?_⟩
  exact P5Core_squareTerm_eq_P5Term x p z

theorem P5_medium_boundary_concrete {α : Type} (x p z : Term α) :
    (((∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z) ∧
      (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z) ∧
      (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z) ∧
      (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z))
     ∧
     (squareTerm (P5Core x p z) = P5Term x p z))
    ∧
    IsMediumSquareAdmissible (P5Core x p z) := by
  refine ⟨?_, P5Core_isMediumSquareAdmissible x p z⟩
  refine ⟨P5_root_excluded_from_R4_patterns_concrete x p z, ?_⟩
  exact P5Core_squareTerm_eq_P5Term x p z

theorem P5_medium_boundary_with_profile {α : Type} (x p z : Term α) :
    (((NoRootInstance sqAbsorbPat (P5Term x p z) ∧
       NoRootInstance sqStablePat (P5Term x p z) ∧
       NoRootInstance decorPat (P5Term x p z) ∧
       NoRootInstance c2c1Pat (P5Term x p z))
      ∧
      (squareTerm (P5Core x p z) = P5Term x p z))
     ∧
     (∃ h : MediumSquareAdmissible (P5Core x p z),
       h.profile =
         ( SelfEmbeddingShape.rightNest
         , SelfEmbeddingShape.leftNest
         , SelfEmbeddingShape.rightNest
         , SelfEmbeddingShape.midNest ))) := by
  refine ⟨?_, ?_⟩
  · refine ⟨P5_root_excluded_from_R4_patterns x p z, ?_⟩
    exact P5Core_squareTerm_eq_P5Term x p z
  · exact P5_medium_profile_witness x p z

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
