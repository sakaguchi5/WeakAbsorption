import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Core.SemanticPackage

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics
namespace Core

open SemanticSystem

structure SemanticComparison (S₁ S₂ : SemanticSystem) where
  targetRel : S₁.Target -> S₂.Target -> Prop
  stateRel  : S₁.State -> S₂.State -> Prop
  kernelRel : S₁.Kernel -> S₂.Kernel -> Prop
  shellRel  : S₁.Shell -> S₂.Shell -> Prop
  regimeRel : S₁.Regime -> S₂.Regime -> Prop
  rowRel    : S₁.Row -> S₂.Row -> Prop
  atomRel   : S₁.Atom -> S₂.Atom -> Prop
  shapeRel  : S₁.Shape -> S₂.Shape -> Prop

  target_to_state_compatible :
    ∀ {tg₁ : S₁.Target} {tg₂ : S₂.Target},
      targetRel tg₁ tg₂ -> stateRel (S₁.targetToState tg₁) (S₂.targetToState tg₂)

  state_to_kernel_compatible :
    ∀ {st₁ : S₁.State} {st₂ : S₂.State},
      stateRel st₁ st₂ -> kernelRel (S₁.stateToKernel st₁) (S₂.stateToKernel st₂)

  state_to_shell_compatible :
    ∀ {st₁ : S₁.State} {st₂ : S₂.State},
      stateRel st₁ st₂ -> shellRel (S₁.stateToShell st₁) (S₂.stateToShell st₂)

  state_to_regime_compatible :
    ∀ {st₁ : S₁.State} {st₂ : S₂.State},
      stateRel st₁ st₂ -> regimeRel (S₁.stateToRegime st₁) (S₂.stateToRegime st₂)

  state_to_row_compatible :
    ∀ {st₁ : S₁.State} {st₂ : S₂.State},
      stateRel st₁ st₂ -> rowRel (S₁.stateToRow st₁) (S₂.stateToRow st₂)

  row_to_atoms_compatible :
    ∀ {row₁ : S₁.Row} {row₂ : S₂.Row},
      rowRel row₁ row₂ ->
        ∀ {a₁ : S₁.Atom}, a₁ ∈ S₁.rowToAtoms row₁ ->
          ∃ a₂ : S₂.Atom, a₂ ∈ S₂.rowToAtoms row₂ ∧ atomRel a₁ a₂

  atoms_to_shape_compatible :
    ∀ {as₁ : List S₁.Atom} {as₂ : List S₂.Atom},
      (∀ {a₁ : S₁.Atom}, a₁ ∈ as₁ -> ∃ a₂ : S₂.Atom, a₂ ∈ as₂ ∧ atomRel a₁ a₂) ->
      ∀ {sh₁ : S₁.Shape}, sh₁ ∈ S₁.atomsToShape as₁ ->
        ∃ sh₂ : S₂.Shape, sh₂ ∈ S₂.atomsToShape as₂ ∧ shapeRel sh₁ sh₂

end Core
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
