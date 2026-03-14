import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.R4.System

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

/-- Canonical package of the `R4System` instance. -/
def r4SystemPackage (tg : R4System.Target) : Core.SemanticPackage R4System tg :=
  Core.canonicalPackage R4System tg

theorem r4System_kernel_matches_observed (tg : CoreKernelTarget) :
    (r4SystemPackage tg).kernel = observedKernel tg := by
  cases tg <;> rfl

theorem r4System_shell_matches_observed (tg : CoreKernelTarget) :
    (r4SystemPackage tg).shell = observedShell tg := by
  cases tg <;> rfl

theorem r4System_state_matches_observed (tg : CoreKernelTarget) :
    (r4SystemPackage tg).state = observedState tg := by
  cases tg <;> rfl

theorem r4System_regime_matches_observed (tg : CoreKernelTarget) :
    (r4SystemPackage tg).regime = observedRegime tg := by
  cases tg <;> rfl

theorem r4System_atoms_eq_rowAtomsOfTarget (tg : CoreKernelTarget) :
    (r4SystemPackage tg).atoms = rowAtomsOfTarget tg := by
  simp [r4SystemPackage, Core.canonicalPackage, R4System, rowAtomsOfTarget,
    stateTarget_r4RealizedStateOf]

theorem r4System_shape_eq_rowShapeOfTarget (tg : CoreKernelTarget) :
    (r4SystemPackage tg).shape = rowShapeOfTarget tg := by
  simp [r4SystemPackage, Core.canonicalPackage, R4System, rowShapeOfAtoms,
    rowShapeOfTarget, rowAtomsOfTarget, stateTarget_r4RealizedStateOf]

theorem r4System_atoms_matches_observed (tg : CoreKernelTarget) :
    (r4SystemPackage tg).atoms = observedRowAtoms tg := by
  rw [r4System_atoms_eq_rowAtomsOfTarget]
  exact rowAtoms_matches_observed tg

theorem r4System_shape_matches_observed (tg : CoreKernelTarget) :
    (r4SystemPackage tg).shape = observedRowShape tg := by
  rw [r4System_shape_eq_rowShapeOfTarget]
  exact rowShape_matches_observed tg

theorem r4System_package_matches_observed (tg : CoreKernelTarget) :
    (r4SystemPackage tg).kernel = (observedSnapshot tg).kernel ∧
    (r4SystemPackage tg).shell = (observedSnapshot tg).shell ∧
    (r4SystemPackage tg).state = (observedSnapshot tg).state ∧
    (r4SystemPackage tg).regime = (observedSnapshot tg).regime ∧
    (r4SystemPackage tg).atoms = (observedSnapshot tg).rowAtoms ∧
    (r4SystemPackage tg).shape = (observedSnapshot tg).rowShape := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact r4System_kernel_matches_observed tg
  · exact r4System_shell_matches_observed tg
  · exact r4System_state_matches_observed tg
  · exact r4System_regime_matches_observed tg
  · exact r4System_atoms_matches_observed tg
  · exact r4System_shape_matches_observed tg

end R4
end Instances
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
