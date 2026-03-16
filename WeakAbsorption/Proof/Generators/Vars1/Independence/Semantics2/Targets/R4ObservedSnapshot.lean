import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.R4KernelObservedSpec

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics2
namespace Targets

open WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4

/-!
Thin observed-data bridge for `Semantics2`.

This module intentionally re-exports only the target-level observed snapshot API needed by the
clean-room side. Bridge theorems and comparison facts stay in the old semantics layer.
-/

abbrev ObservedShapeFamily := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.ObservedShapeFamily

abbrev ObservedKernelSnapshot := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.ObservedKernelSnapshot

abbrev observedKernel := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedKernel

abbrev observedShell := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedShell

abbrev observedState := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedState

abbrev observedRegime := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedRegime

abbrev observedRowAtoms := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedRowAtoms

abbrev observedRowShape := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedRowShape

abbrev observedShapeFamily := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedShapeFamily

abbrev observedSnapshot := WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.observedSnapshot

end Targets
end Semantics2
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
