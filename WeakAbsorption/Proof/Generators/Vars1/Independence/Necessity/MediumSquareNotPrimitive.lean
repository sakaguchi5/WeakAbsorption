import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareReduction

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
Concrete root-seed notion for the current primitive R4 families.
A term is a primitive R4 root-seed if it is equal to one of the four
concrete primitive root forms.
-/
def IsPrimitiveR4RootSeed {α : Type} (T : Term α) : Prop :=
  (∃ t u : Term α, ((t.op u).op (u.op u)) = T) ∨
  ((∃ t u : Term α, (((t.op u).op (u.op u)).op u) = T) ∨
   ((∃ t u : Term α, ((t.op u).op (u.op (u.op u))) = T) ∨
    (∃ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) = T)))

theorem mediumSquareBoundary_not_primitiveR4RootSeed {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T) :
    ¬ IsPrimitiveR4RootSeed T := by
  intro hSeed
  rcases mediumSquareBoundary_concrete_exclusion h with ⟨hSA, hSS, hD, hC⟩
  rcases hSeed with hSASeed | hRest
  · rcases hSASeed with ⟨t, u, hEq⟩
    exact (hSA t u) hEq
  · rcases hRest with hSSSeed | hRest
    · rcases hSSSeed with ⟨t, u, hEq⟩
      exact (hSS t u) hEq
    · rcases hRest with hDSeed | hCSeed
      · rcases hDSeed with ⟨t, u, hEq⟩
        exact (hD t u) hEq
      · rcases hCSeed with ⟨x0, p0, z0, hEq⟩
        exact (hC x0 p0 z0) hEq

/--
Generic reclassification principle:
a medium square boundary term has a square core and is not a primitive
R4 root-seed.
-/
theorem mediumSquareBoundary_reclassified {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T) :
    ∃ L : Term α, squareTerm L = T ∧ ¬ IsPrimitiveR4RootSeed T := by
  rcases mediumSquareBoundary_reduction_principle h with
    ⟨L, hSq, hRigid, hSA, hSS, hD, hC⟩
  refine ⟨L, hSq, ?_⟩
  exact mediumSquareBoundary_not_primitiveR4RootSeed h

/--
A medium square boundary term has a canonical square core and lies outside
the current primitive R4 root-seed class.
-/
theorem mediumSquareBoundary_square_outsider {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T) :
    (∃ L : Term α, squareTerm L = T) ∧ ¬ IsPrimitiveR4RootSeed T := by
  rcases mediumSquareBoundary_reclassified h with ⟨L, hSq, hNot⟩
  exact ⟨⟨L, hSq⟩, hNot⟩

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
