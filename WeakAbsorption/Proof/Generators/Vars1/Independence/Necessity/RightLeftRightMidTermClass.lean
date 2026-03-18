import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareProfileClass

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
A term belongs to the right/left/right/mid profile class if it is represented
by some medium square boundary object having that obstruction profile.
-/
def IsRightLeftRightMidTerm {α : Type} (T : Term α) : Prop :=
  ∃ B : MediumSquareBoundary α,
    RightLeftRightMidProfile B ∧
    B.term = T

theorem rightLeftRightMidTerm_square_outsider {α : Type} {T : Term α}
    (h : IsRightLeftRightMidTerm T) :
    (∃ L : Term α, squareTerm L = T) ∧
    ¬ IsPrimitiveR4RootSeed T := by
  exact rightLeftRightMidProfile_square_outsider h

theorem rightLeftRightMidTerm_has_core {α : Type} {T : Term α}
    (h : IsRightLeftRightMidTerm T) :
    ∃ L : Term α, squareTerm L = T := by
  exact (rightLeftRightMidTerm_square_outsider h).1

theorem rightLeftRightMidTerm_not_primitive_seed {α : Type} {T : Term α}
    (h : IsRightLeftRightMidTerm T) :
    ¬ IsPrimitiveR4RootSeed T := by
  exact (rightLeftRightMidTerm_square_outsider h).2

theorem rightLeftRightMidTerm_unique_root_core {α : Type} {T : Term α}
    (h : IsRightLeftRightMidTerm T) :
    ∃ L : Term α,
      squareTerm L = T ∧
      ∀ {t u : Term α}, t.op u = T ↔ t = L ∧ u = L := by
  rcases h with ⟨B, hProf, hT⟩
  refine ⟨B.core, ?_, ?_⟩
  · have hsq : squareTerm B.core = B.term := by
      exact (B.root_decomposition_iff.mpr ⟨rfl, rfl⟩)
    exact hsq.trans hT
  · intro t u
    constructor
    · intro hEq
      rw [← hT] at hEq
      exact B.root_decomposition_iff.mp hEq
    · rintro ⟨rfl, rfl⟩
      exact (B.root_decomposition_iff.mpr ⟨rfl, rfl⟩).trans hT

theorem rightLeftRightMidTerm_children_equal {α : Type} {T : Term α}
    (h : IsRightLeftRightMidTerm T)
    {t u : Term α} (hEq : t.op u = T) :
    t = u := by
  rcases rightLeftRightMidTerm_unique_root_core h with ⟨L, hSq, hRigid⟩
  rcases (hRigid.mp hEq) with ⟨ht, hu⟩
  rw [ht, hu]

/--
A bundled generic summary for terms in the right/left/right/mid profile class.
-/
theorem rightLeftRightMidTerm_summary {α : Type} {T : Term α}
    (h : IsRightLeftRightMidTerm T) :
    (∃ L : Term α, squareTerm L = T ∧
        ∀ {t u : Term α}, t.op u = T ↔ t = L ∧ u = L) ∧
    ¬ IsPrimitiveR4RootSeed T := by
  refine ⟨rightLeftRightMidTerm_unique_root_core h, ?_⟩
  exact rightLeftRightMidTerm_not_primitive_seed h

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
