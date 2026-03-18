import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.SquareAdmissibility
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_R4_PatternExclusion
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_R4S_SquareSchemaAudit

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5Core_squareTerm_eq_P5Term {α : Type} (x p z : Term α) :
    squareTerm (P5Core x p z) = P5Term x p z := by
  simp [squareTerm, P5Core, P5Term]

theorem P5Core_root_rigid {α : Type} (x p z : Term α) :
    ∀ {t u : Term α}, t.op u = squareTerm (P5Core x p z) →
      t = P5Core x p z ∧ u = P5Core x p z := by
  intro t u h
  dsimp [squareTerm] at h
  injection h with ht hu
  exact ⟨ht, hu⟩

theorem P5Core_weakSquareAdmissible {α : Type} (x p z : Term α) :
    WeakSquareAdmissible (P5Core x p z) := by
  refine
    { root_rigid := P5Core_root_rigid x p z
      no_sqAbsorb := ?_
      no_sqStable := ?_
      no_decor := ?_
      no_c2c1 := ?_ }
  · simpa [squareTerm, P5Core, P5Term] using
      (no_sqAbsorb_root_P5 (x := x) (p := p) (z := z))
  · simpa [squareTerm, P5Core, P5Term] using
      (no_sqStable_root_P5 (x := x) (p := p) (z := z))
  · simpa [squareTerm, P5Core, P5Term] using
      (no_decor_root_P5 (x := x) (p := p) (z := z))
  · simpa [squareTerm, P5Core, P5Term] using
      (no_c2c1_root_P5 (x := x) (p := p) (z := z))

def P5Core_mediumSquareAdmissible {α : Type} (x p z : Term α) :
    MediumSquareAdmissible (P5Core x p z) := by
  refine
    { toWeak := P5Core_weakSquareAdmissible x p z
      sqAbsorb_shape := SelfEmbeddingShape.rightNest
      sqStable_shape := SelfEmbeddingShape.leftNest
      decor_shape := SelfEmbeddingShape.rightNest
      c2c1_shape := SelfEmbeddingShape.midNest }

theorem P5Core_isMediumSquareAdmissible {α : Type} (x p z : Term α) :
    IsMediumSquareAdmissible (P5Core x p z) := by
  exact ⟨P5Core_mediumSquareAdmissible x p z⟩

theorem P5Core_medium_profile {α : Type} (x p z : Term α) :
    (P5Core_mediumSquareAdmissible (x := x) (p := p) (z := z)).profile =
      ( SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.leftNest
      , SelfEmbeddingShape.rightNest
      , SelfEmbeddingShape.midNest ) := by
  rfl

theorem P5Term_is_square_of_medium_admissible_core {α : Type} (x p z : Term α) :
    squareTerm (P5Core x p z) = P5Term x p z := by
  exact P5Core_squareTerm_eq_P5Term x p z

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
