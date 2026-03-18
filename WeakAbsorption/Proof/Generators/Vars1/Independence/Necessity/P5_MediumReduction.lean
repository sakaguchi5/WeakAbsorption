import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.MediumSquareReduction
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_MediumSquareBoundaryInstance

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5_medium_reduction_principle {α : Type} (x p z : Term α) :
    ∃ L : Term α,
      squareTerm L = P5Term x p z ∧
      (∀ {t u : Term α}, t.op u = P5Term x p z → t = L ∧ u = L) ∧
      NoRootInstance sqAbsorbPat (P5Term x p z) ∧
      NoRootInstance sqStablePat (P5Term x p z) ∧
      NoRootInstance decorPat (P5Term x p z) ∧
      NoRootInstance c2c1Pat (P5Term x p z) := by
  exact mediumSquareBoundary_reduction_principle (P5_isMediumSquareBoundary x p z)

theorem P5_medium_concrete_exclusion {α : Type} (x p z : Term α) :
    (∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z) ∧
    (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z) ∧
    (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z) ∧
    (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z) := by
  exact mediumSquareBoundary_concrete_exclusion (P5_isMediumSquareBoundary x p z)

theorem P5_medium_unique_root_core {α : Type} (x p z : Term α) :
    ∃ L : Term α,
      squareTerm L = P5Term x p z ∧
      ∀ {t u : Term α}, t.op u = P5Term x p z ↔ t = L ∧ u = L := by
  exact mediumSquareBoundary_unique_root_core (P5_isMediumSquareBoundary x p z)

theorem P5_medium_children_equal {α : Type} (x p z : Term α)
    {t u : Term α} (hEq : t.op u = P5Term x p z) :
    t = u := by
  exact mediumSquareBoundary_children_equal (P5_isMediumSquareBoundary x p z) hEq

/--
A fully bundled P5-specific medium reduction summary.
-/
theorem P5_medium_reduction_summary {α : Type} (x p z : Term α) :
    (∃ L : Term α,
      squareTerm L = P5Term x p z ∧
      ∀ {t u : Term α}, t.op u = P5Term x p z ↔ t = L ∧ u = L)
    ∧
    ((∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z) ∧
     (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z) ∧
     (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z) ∧
     (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z)) := by
  refine ⟨P5_medium_unique_root_core x p z, P5_medium_concrete_exclusion x p z⟩

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
