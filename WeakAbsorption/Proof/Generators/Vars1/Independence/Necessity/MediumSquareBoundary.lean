import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.SquareAdmissibility

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
A medium square boundary object consists of:
- a core term,
- a medium square-admissibility witness for that core.
This is data, so it lives in `Type`, not `Prop`.
-/
structure MediumSquareBoundary (α : Type) where
  core : Term α
  admissible : MediumSquareAdmissible core

/-- The square term represented by a boundary object. -/
def MediumSquareBoundary.term {α : Type} (B : MediumSquareBoundary α) : Term α :=
  squareTerm B.core

/-- The obstruction profile carried by a boundary object. -/
def MediumSquareBoundary.profile {α : Type} (B : MediumSquareBoundary α) :
    SelfEmbeddingShape × SelfEmbeddingShape × SelfEmbeddingShape × SelfEmbeddingShape :=
  B.admissible.profile

/-- A term is a medium square boundary term if it is the square represented by some boundary object. -/
def IsMediumSquareBoundary {α : Type} (T : Term α) : Prop :=
  ∃ B : MediumSquareBoundary α, B.term = T

theorem MediumSquareBoundary.root_rigid {α : Type} (B : MediumSquareBoundary α) :
    ∀ {t u : Term α}, t.op u = B.term → t = B.core ∧ u = B.core := by
  intro t u h
  exact B.admissible.toWeak.root_rigid h

theorem MediumSquareBoundary.root_decomposition_iff {α : Type}
    (B : MediumSquareBoundary α) {t u : Term α} :
    t.op u = B.term ↔ t = B.core ∧ u = B.core := by
  exact WeakSquareAdmissible.root_decomposition_iff B.admissible.toWeak

theorem MediumSquareBoundary.children_equal {α : Type}
    (B : MediumSquareBoundary α) {t u : Term α}
    (h : t.op u = B.term) :
    t = u := by
  exact WeakSquareAdmissible.children_equal B.admissible.toWeak h

theorem IsMediumSquareBoundary.exists_core {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T) :
    ∃ B : MediumSquareBoundary α, squareTerm B.core = T := by
  rcases h with ⟨B, hB⟩
  exact ⟨B, hB⟩

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
