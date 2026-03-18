import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_R4S_SquareSchemaAudit
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity
open ProofCore

theorem P5Term_eq_core_square {α : Type} (x p z : Term α) :
    P5Term x p z = (P5Core x p z).op (P5Core x p z) := by
  simpa using P5Term_eq_square_of_core x p z

theorem P5_core_is_explicit {α : Type} (x p z : Term α) :
    P5Core x p z = (x.op (p.op z)).op z := by
  rfl

theorem P5_square_schema_reduction {α : Type} (x p z : Term α) :
    ∃ t : Term α, P5Term x p z = t.op t := by
  refine ⟨P5Core x p z, ?_⟩
  simpa using P5Term_eq_core_square x p z

theorem P5_bridge_summary {α : Type} (x p z : Term α) :
    (NoRootInstance sqAbsorbPat (P5Term x p z) ∧
     NoRootInstance sqStablePat (P5Term x p z) ∧
     NoRootInstance decorPat (P5Term x p z) ∧
     NoRootInstance c2c1Pat (P5Term x p z))
    ∧
    (∃ t : Term α, P5Term x p z = t.op t) := by
  refine ⟨P5_root_excluded_from_R4_patterns x p z, ?_⟩
  exact P5_square_schema_reduction x p z

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
