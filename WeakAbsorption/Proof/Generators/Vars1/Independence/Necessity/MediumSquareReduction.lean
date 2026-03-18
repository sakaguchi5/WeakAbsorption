import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareBoundary

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
A generic reduction principle for medium square boundary terms:

if `T` is represented by a medium square boundary object, then
- `T` has a square core,
- its root decomposition is rigid,
- it is excluded from the current four primitive R4 root-pattern families.
-/
theorem mediumSquareBoundary_reduction_principle {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T) :
    ∃ L : Term α,
      squareTerm L = T ∧
      (∀ {t u : Term α}, t.op u = T → t = L ∧ u = L) ∧
      NoRootInstance sqAbsorbPat T ∧
      NoRootInstance sqStablePat T ∧
      NoRootInstance decorPat T ∧
      NoRootInstance c2c1Pat T := by
  rcases h with ⟨B, hB⟩
  refine ⟨B.core, hB, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u hEq
    rw [← hB] at hEq
    exact B.root_rigid hEq
  · rw [← hB]
    exact B.admissible.toWeak.no_sqAbsorb
  · rw [← hB]
    exact B.admissible.toWeak.no_sqStable
  · rw [← hB]
    exact B.admissible.toWeak.no_decor
  · rw [← hB]
    exact B.admissible.toWeak.no_c2c1

/--
Concrete root-form exclusion derived from the generic reduction principle.
-/
theorem mediumSquareBoundary_concrete_exclusion {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T) :
    (∀ t u : Term α, ((t.op u).op (u.op u)) ≠ T) ∧
    (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ T) ∧
    (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ T) ∧
    (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ T) := by
  rcases mediumSquareBoundary_reduction_principle h with
    ⟨L, hSq, hRigid, hSA, hSS, hD, hC⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using
      (no_sqAbsorb_root_eq_of_no_instance (target := T) hSA)
  · simpa using
      (no_sqStable_root_eq_of_no_instance (target := T) hSS)
  · simpa using
      (no_decor_root_eq_of_no_instance (target := T) hD)
  · simpa using
      (no_c2c1_root_eq_of_no_instance (target := T) hC)

/--
The square core extracted from a medium square boundary term is unique at the root.
-/
theorem mediumSquareBoundary_unique_root_core {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T) :
    ∃ L : Term α,
      squareTerm L = T ∧
      ∀ {t u : Term α}, t.op u = T ↔ t = L ∧ u = L := by
  rcases mediumSquareBoundary_reduction_principle h with
    ⟨L, hSq, hRigid, hSA, hSS, hD, hC⟩
  refine ⟨L, hSq, ?_⟩
  intro t u
  constructor
  · intro hEq
    exact hRigid hEq
  · rintro ⟨rfl, rfl⟩
    dsimp [squareTerm] at hSq
    exact hSq
/--
A medium square boundary term has equal children in every root decomposition.
-/
theorem mediumSquareBoundary_children_equal {α : Type} {T : Term α}
    (h : IsMediumSquareBoundary T)
    {t u : Term α} (hEq : t.op u = T) :
    t = u := by
  rcases mediumSquareBoundary_reduction_principle h with
    ⟨L, hSq, hRigid, hSA, hSS, hD, hC⟩
  rcases hRigid hEq with ⟨ht, hu⟩
  rw [ht, hu]

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
