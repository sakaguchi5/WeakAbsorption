import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareBoundaryUniqueness
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_RightLeftRightMidTermClass

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5_core_unique_from_square_presentations {α : Type} (x p z : Term α) :
    ∀ {L : Term α},
      squareTerm L = P5Term x p z →
      L = P5Core x p z := by
  intro L hL
  exact rightLeftRightMidTerm_core_unique
    (P5_isRightLeftRightMidTerm x p z)
    hL
    (P5Core_squareTerm_eq_P5Term x p z)

theorem P5_profile_witness_core_rigid {α : Type} (x p z : Term α)
    {B : MediumSquareBoundary α}
    (hTerm : B.term = P5Term x p z) :
    B.core = P5Core x p z := by
  have hsame :
      B.term = (P5_mediumSquareBoundary x p z).term := by
    simpa [P5_mediumSquareBoundary_term x p z] using hTerm
  have hcore :
      B.core = (P5_mediumSquareBoundary x p z).core := by
    exact
      mediumSquareBoundary_core_unique_of_same_term
        (B₁ := B) (B₂ := P5_mediumSquareBoundary x p z) hsame
  simpa [P5Core] using hcore

theorem P5_profile_witness_unique_core {α : Type} (x p z : Term α)
    (h : ∃ B : MediumSquareBoundary α,
      RightLeftRightMidProfile B ∧ B.term = P5Term x p z) :
    let B := Classical.choose h
    B.core = P5Core x p z := by
  classical
  let B : MediumSquareBoundary α := Classical.choose h
  have hTerm : B.term = P5Term x p z := by
    simpa [B] using (Classical.choose_spec h).2
  simpa [B] using
    (P5_profile_witness_core_rigid (x := x) (p := p) (z := z) (B := B) hTerm)

theorem P5_profile_class_canonical_core {α : Type} (x p z : Term α) :
    ∀ {L : Term α},
      (∃ B : MediumSquareBoundary α,
        RightLeftRightMidProfile B ∧
        B.term = P5Term x p z ∧
        B.core = L) →
      L = P5Core x p z := by
  intro L hL
  rcases hL with ⟨B, hProf, hTerm, hCore⟩
  have hB : B.core = P5Core x p z := by
    exact P5_profile_witness_core_rigid x p z hTerm
  exact hCore.symm.trans hB

theorem P5_rightLeftRightMid_canonical_summary {α : Type} (x p z : Term α) :
    IsRightLeftRightMidTerm (P5Term x p z) ∧
    (∀ {L : Term α}, squareTerm L = P5Term x p z → L = P5Core x p z) := by
  refine ⟨P5_isRightLeftRightMidTerm x p z, ?_⟩
  intro L hL
  exact P5_core_unique_from_square_presentations x p z hL

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
