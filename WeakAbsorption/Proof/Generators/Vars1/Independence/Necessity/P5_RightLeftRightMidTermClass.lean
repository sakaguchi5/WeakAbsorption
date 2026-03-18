import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.RightLeftRightMidTermClass
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_ProfileClass

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore

theorem P5_isRightLeftRightMidTerm {α : Type} (x p z : Term α) :
    IsRightLeftRightMidTerm (P5Term x p z) := by
  exact P5_profileClass_boundary_witness x p z

theorem P5_rightLeftRightMid_square_outsider {α : Type} (x p z : Term α) :
    (∃ L : Term α, squareTerm L = P5Term x p z) ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  exact rightLeftRightMidTerm_square_outsider (P5_isRightLeftRightMidTerm x p z)

theorem P5_rightLeftRightMid_unique_root_core {α : Type} (x p z : Term α) :
    ∃ L : Term α,
      squareTerm L = P5Term x p z ∧
      ∀ {t u : Term α}, t.op u = P5Term x p z ↔ t = L ∧ u = L := by
  exact rightLeftRightMidTerm_unique_root_core (P5_isRightLeftRightMidTerm x p z)

theorem P5_rightLeftRightMid_children_equal {α : Type} (x p z : Term α)
    {t u : Term α} (hEq : t.op u = P5Term x p z) :
    t = u := by
  exact rightLeftRightMidTerm_children_equal (P5_isRightLeftRightMidTerm x p z) hEq

theorem P5_rightLeftRightMid_summary {α : Type} (x p z : Term α) :
    (∃ L : Term α, squareTerm L = P5Term x p z ∧
        ∀ {t u : Term α}, t.op u = P5Term x p z ↔ t = L ∧ u = L) ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  exact rightLeftRightMidTerm_summary (P5_isRightLeftRightMidTerm x p z)

theorem P5_rightLeftRightMid_summary_canonical {α : Type} (x p z : Term α) :
    squareTerm (P5Core x p z) = P5Term x p z ∧
    ¬ IsPrimitiveR4RootSeed (P5Term x p z) := by
  refine ⟨P5Core_squareTerm_eq_P5Term x p z, ?_⟩
  exact (P5_rightLeftRightMid_summary x p z).2

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
