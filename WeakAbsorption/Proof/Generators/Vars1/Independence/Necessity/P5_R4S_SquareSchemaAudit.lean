import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.P5_R4_PatternExclusion
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore


namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open ProofCore
/-
`P5_R4_PatternExclusion.lean` で確定したのは次の二点：
1. `P5` は既存 R4 の 4 pattern family の root instance ではない。
2. `P5` は canonical whole-fragment self-square である。

このファイルでは、まだ `P5` を positive に `DoubleSq` へ還元しない。
ここで固定するのは、`P5` を new family seed ではなく
square-schema audit の対象として扱うための弱い整理だけである。
-/

/-- The canonical square core appearing in `P5`. -/
def P5Core {α : Type} (x p z : Term α) : Term α :=
  (x.op (p.op z)).op z

theorem P5Term_eq_square_of_core {α : Type} (x p z : Term α) :
    P5Term x p z = (P5Core x p z).op (P5Core x p z) := by
  simp [P5Term, P5Core]

theorem P5Core_def {α : Type} (x p z : Term α) :
    P5Core x p z = (x.op (p.op z)).op z := by
  rfl



/--
A bundled summary of the negative R4-pattern audit plus the positive
square-core observation.
-/
theorem P5_R4_audit_summary {α : Type} (x p z : Term α) :
    (NoRootInstance sqAbsorbPat (P5Term x p z) ∧
     NoRootInstance sqStablePat (P5Term x p z) ∧
     NoRootInstance decorPat (P5Term x p z) ∧
     NoRootInstance c2c1Pat (P5Term x p z))
    ∧
    (∃ L : Term α, L = P5Core x p z ∧ P5Term x p z = L.op L) := by
  refine ⟨P5_root_excluded_from_R4_patterns x p z, ?_⟩
  refine ⟨P5Core x p z, rfl, ?_⟩
  simpa [P5Core] using P5Term_eq_square_of_core x p z

/--
Concrete form of the same summary: `P5` avoids all four existing R4 root
patterns and has a canonical square core.
-/
theorem P5_R4_concrete_audit_summary {α : Type} (x p z : Term α) :
    ((∀ t u : Term α, ((t.op u).op (u.op u)) ≠ P5Term x p z) ∧
     (∀ t u : Term α, (((t.op u).op (u.op u)).op u) ≠ P5Term x p z) ∧
     (∀ t u : Term α, ((t.op u).op (u.op (u.op u))) ≠ P5Term x p z) ∧
     (∀ x0 p0 z0 : Term α, (((x0.op (p0.op z0)).op z0).op (p0.op z0)) ≠ P5Term x p z))
    ∧
    (P5Term x p z = (P5Core x p z).op (P5Core x p z)) := by
  refine ⟨P5_root_excluded_from_R4_patterns_concrete x p z, ?_⟩
  simpa using P5Term_eq_square_of_core x p z

/--
This is the key classification boundary now justified by the current audit:
before proving any positive `R4S`/`DoubleSq` statement, `P5` should be read
as a square-schema candidate, not as an additional R4-family instance.
-/
theorem P5_is_not_an_existing_R4_family_but_has_square_schema {α : Type} (x p z : Term α) :
    (NoRootInstance sqAbsorbPat (P5Term x p z) ∧
     NoRootInstance sqStablePat (P5Term x p z) ∧
     NoRootInstance decorPat (P5Term x p z) ∧
     NoRootInstance c2c1Pat (P5Term x p z))
    ∧
    P5Term x p z = (P5Core x p z).op (P5Core x p z) := by
  refine ⟨P5_root_excluded_from_R4_patterns x p z, ?_⟩
  simpa using P5Term_eq_square_of_core x p z

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
