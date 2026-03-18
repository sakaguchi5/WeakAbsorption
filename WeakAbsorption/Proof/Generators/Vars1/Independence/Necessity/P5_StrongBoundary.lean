import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_Status

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

/--
Any root decomposition of `P5` is forced to be exactly the canonical square
decomposition `P5Core ⋆ P5Core`.
-/
theorem P5_root_decomposition_unique {α : Type} (x p z : Term α)
    {t u : Term α} (h : t.op u = P5Term x p z) :
    t = P5Core x p z ∧ u = P5Core x p z := by
  rw [P5Term_eq_core_square (x := x) (p := p) (z := z)] at h
  injection h with ht hu
  exact ⟨ht, hu⟩

/--
Root decomposition of `P5` is equivalent to being the canonical square core
on both sides.
-/
theorem P5_root_decomposition_iff {α : Type} (x p z : Term α)
    {t u : Term α} :
    t.op u = P5Term x p z ↔
      t = P5Core x p z ∧ u = P5Core x p z := by
  constructor
  · intro h
    exact P5_root_decomposition_unique x p z h
  · rintro ⟨rfl, rfl⟩
    simpa using (P5Term_eq_core_square (x := x) (p := p) (z := z)).symm

/--
In particular, any root decomposition of `P5` is a square decomposition.
-/
theorem P5_root_children_equal {α : Type} (x p z : Term α)
    {t u : Term α} (h : t.op u = P5Term x p z) :
    t = u := by
  rcases P5_root_decomposition_unique x p z h with ⟨ht, hu⟩
  rw [ht, hu]

/--
The left child of any root decomposition of `P5` is forced to be the canonical core.
-/
theorem P5_root_left_forced {α : Type} (x p z : Term α)
    {t u : Term α} (h : t.op u = P5Term x p z) :
    t = P5Core x p z := by
  exact (P5_root_decomposition_unique x p z h).1

/--
The right child of any root decomposition of `P5` is forced to be the canonical core.
-/
theorem P5_root_right_forced {α : Type} (x p z : Term α)
    {t u : Term α} (h : t.op u = P5Term x p z) :
    u = P5Core x p z := by
  exact (P5_root_decomposition_unique x p z h).2

/--
Strong boundary theorem for `P5`:
it is outside the four existing R4 root-pattern families, and its root
decomposition is uniquely the canonical square `P5Core ⋆ P5Core`.
-/
theorem P5_strong_boundary {α : Type} (x p z : Term α) :
    (NoRootInstance sqAbsorbPat (P5Term x p z) ∧
     NoRootInstance sqStablePat (P5Term x p z) ∧
     NoRootInstance decorPat (P5Term x p z) ∧
     NoRootInstance c2c1Pat (P5Term x p z))
    ∧
    (∀ {t u : Term α},
      t.op u = P5Term x p z ↔
        t = P5Core x p z ∧ u = P5Core x p z) := by
  refine ⟨P5_root_excluded_from_R4_patterns x p z, ?_⟩
  intro t u
  exact P5_root_decomposition_iff x p z

/--
Concrete version: `P5` avoids all four concrete R4 root forms and every
root decomposition is the unique canonical square decomposition.
-/
theorem P5_strong_boundary_concrete {α : Type} (x p z : Term α) :
    ((∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z) ∧
     (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z) ∧
     (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z) ∧
     (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z))
    ∧
    (∀ {t u : Term α},
      t.op u = P5Term x p z →
        t = P5Core x p z ∧ u = P5Core x p z) := by
  refine ⟨P5_root_excluded_from_R4_patterns_concrete x p z, ?_⟩
  intro t u h
  exact P5_root_decomposition_unique x p z h

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
