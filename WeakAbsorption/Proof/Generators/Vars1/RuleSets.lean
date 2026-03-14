import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1

open WeakAbsorption.Spec

/--
Centralized RuleSet aliases for vars=1 workstreams.

Naming policy:
- `R2`, `R3`, `R4` are the proof-facing cores.
- `R4S` is `R4` plus the optional shortcut rule `DoubleSq`.
- `R5` is kept only as a backwards-compatible alias for `R4S`.
-/
abbrev R2 : RuleSet :=
  [RuleId.SqAbsorb, RuleId.SqStable]

abbrev R3 : RuleSet :=
  [RuleId.SqAbsorb, RuleId.SqStable, RuleId.Decor]

abbrev R4 : RuleSet :=
  [RuleId.SqAbsorb, RuleId.SqStable, RuleId.Decor, RuleId.C2C1]

/-- `R4` plus the derived/shortcut rule `DoubleSq` (tooling/search convenience). -/
abbrev R4S : RuleSet :=
  [RuleId.SqAbsorb, RuleId.SqStable, RuleId.Decor, RuleId.C2C1, RuleId.DoubleSq]

/-- Backwards-compatible alias. Prefer `R4` or `R4S`. -/
-- Use `Vars1.R4` (core) or `Vars1.R4S` (core+shortcut). `R5` is retained only for compatibility.
@[deprecated "Vars1.R4` or `Vars1.R4S" (since := "2026-03-06")]
abbrev R5 : RuleSet := R4S
end Vars1
end Generators
end Proof
end WeakAbsorption
