import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Core.Main
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.R4KernelObservedSpec

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics
namespace Instances
namespace R4

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore
open Core

/-- Forget tags and keep only slot × channel incidence. -/
def rowShapeOfAtoms (atoms : List RowAtom) : List RowShapeCoord :=
  (atoms.map (fun a => (a.slot, a.channel))).eraseDups

/-- The current audited `R4` semantics, re-expressed as one `SemanticSystem`. -/
def R4System : Core.SemanticSystem :=
  { Target := CoreKernelTarget
    Kernel := CoreKernelClass
    Shell := CoreKernelShell
    State := CoreRealizedState
    Regime := CoreKernelRegime
    Row := PurifiedCtxRow
    Atom := RowAtom
    Shape := RowShapeCoord

    targetToState := r4RealizedStateOf
    stateToKernel := fun st => coreKernelClass (stateTarget st)
    stateToShell := fun st => coreKernelShell (stateTarget st)
    stateToRegime := fun st => packageRegime (stateTarget st)
    stateToRow := fun st => packageRow (stateTarget st)
    rowToAtoms := rowAtomsOfRow
    atomsToShape := rowShapeOfAtoms

    targetExt := fun a b => a = b
    kernelExt := fun a b => a = b
    shellExt := fun a b => a = b
    stateExt := fun a b => a = b
    regimeExt := fun a b => a = b
    rowExt := fun a b => a = b
    atomsExt := fun a b => a = b
    shapeExt := fun a b => a = b }

end R4
end Instances
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
