import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4KernelRegistry
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_SemanticPackage

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Core

abbrev ObservedTarget := Necessity.CoreKernelTarget
abbrev ObservedKernelClass := Necessity.CoreKernelClass
abbrev ObservedShellKind := Necessity.CoreKernelShell
abbrev ObservedState := Necessity.CoreRealizedState
abbrev ObservedRegime := Necessity.CoreKernelRegime

/-- Coarse observed rule-kind, intentionally separated from legacy `RowSlot`. -/
inductive ObservedRuleKind where
  | sqAbsorb
  | sqStable
  | decor
  | c2c1
  deriving DecidableEq, Repr

/-- Coarse observed side, intentionally separated from legacy `CtxChannel`. -/
inductive ObservedSide where
  | root
  | left
  | right
  deriving DecidableEq, Repr

/--
Coarse family labels for the current audited R4 row-geometry sector.

Note:
- `sameCoordDuplication` intentionally avoids legacy wording like
  "sameSlotSameChannelDuplication".
-/
inductive ObservedShapeFamily where
  | singleton
  | sameCoordDuplication
  | rootMixedPure
  | bridgeSplitMixed
  deriving DecidableEq, Repr

end Core
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
