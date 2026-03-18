import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_R4_PatternExclusion
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_R4S_SquareSchemaAudit
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_DoubleSqBridge
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity
open ProofCore

/--
Current certified status of `P5`.

What is already proved:
1. `P5` is excluded from all four existing R4 root-pattern families.
2. `P5` has a canonical whole-fragment square core.
3. Hence `P5` should be treated as a square-schema audit target,
   not as an additional existing R4-family instance.

What is intentionally *not* claimed here:
- no positive reduction to `DoubleSq`;
- no claim that `P5` is already absorbed by existing R4S theorems.
-/
theorem P5_certified_status {α : Type} (x p z : Term α) :
    ((NoRootInstance sqAbsorbPat (P5Term x p z) ∧
      NoRootInstance sqStablePat (P5Term x p z) ∧
      NoRootInstance decorPat (P5Term x p z) ∧
      NoRootInstance c2c1Pat (P5Term x p z))
     ∧
     (P5Term x p z = (P5Core x p z).op (P5Core x p z))) := by
  exact P5_is_not_an_existing_R4_family_but_has_square_schema x p z

/--
Concrete root-form exclusion plus canonical square-core presentation.
-/
theorem P5_certified_status_concrete {α : Type} (x p z : Term α) :
    (((∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z) ∧
      (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z) ∧
      (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z) ∧
      (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z))
     ∧
     (P5Term x p z = (P5Core x p z).op (P5Core x p z))) := by
  exact P5_R4_concrete_audit_summary x p z

/--
Canonical existential square presentation.
-/
theorem P5_has_certified_square_schema {α : Type} (x p z : Term α) :
    ∃ t : Term α, P5Term x p z = t.op t := by
  exact P5_square_schema_reduction x p z

/--
Boundary theorem: at the current audited stage, `P5` is certified as
an outsider to the existing R4 pattern families and an inhabitant of
the square-schema class.
-/
theorem P5_classification_boundary {α : Type} (x p z : Term α) :
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
