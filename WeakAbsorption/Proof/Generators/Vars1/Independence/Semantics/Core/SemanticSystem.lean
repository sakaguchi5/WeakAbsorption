namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics
namespace Core

/-!
A rule-relative semantic system.

Design principles:
- the architecture should not be tied to `R4` permanently,
- concrete instances should plug into this interface,
- future comparison work should treat systems as first-class objects.
-/

structure SemanticSystem where
  Target : Type
  Kernel : Type
  Shell : Type
  State : Type
  Regime : Type
  Row : Type
  Atom : Type
  Shape : Type

  targetToState : Target -> State
  stateToKernel : State -> Kernel
  stateToShell : State -> Shell
  stateToRegime : State -> Regime
  stateToRow : State -> Row
  rowToAtoms : Row -> List Atom
  atomsToShape : List Atom -> List Shape

  targetExt : Target -> Target -> Prop
  kernelExt : Kernel -> Kernel -> Prop
  shellExt : Shell -> Shell -> Prop
  stateExt : State -> State -> Prop
  regimeExt : Regime -> Regime -> Prop
  rowExt : Row -> Row -> Prop
  atomsExt : List Atom -> List Atom -> Prop
  shapeExt : List Shape -> List Shape -> Prop

namespace SemanticSystem

def targetToKernel (S : SemanticSystem) (tg : S.Target) : S.Kernel :=
  S.stateToKernel (S.targetToState tg)

def targetToShell (S : SemanticSystem) (tg : S.Target) : S.Shell :=
  S.stateToShell (S.targetToState tg)

def targetToRegime (S : SemanticSystem) (tg : S.Target) : S.Regime :=
  S.stateToRegime (S.targetToState tg)

def targetToRow (S : SemanticSystem) (tg : S.Target) : S.Row :=
  S.stateToRow (S.targetToState tg)

def targetToAtoms (S : SemanticSystem) (tg : S.Target) : List S.Atom :=
  S.rowToAtoms (targetToRow S tg)

def targetToShape (S : SemanticSystem) (tg : S.Target) : List S.Shape :=
  S.atomsToShape (targetToAtoms S tg)

def stateToAtoms (S : SemanticSystem) (st : S.State) : List S.Atom :=
  S.rowToAtoms (S.stateToRow st)

def stateToShape (S : SemanticSystem) (st : S.State) : List S.Shape :=
  S.atomsToShape (stateToAtoms S st)

def sameKernel (S : SemanticSystem) (tg₁ tg₂ : S.Target) : Prop :=
  S.kernelExt (targetToKernel S tg₁) (targetToKernel S tg₂)

def sameShell (S : SemanticSystem) (tg₁ tg₂ : S.Target) : Prop :=
  S.shellExt (targetToShell S tg₁) (targetToShell S tg₂)

def sameRegime (S : SemanticSystem) (tg₁ tg₂ : S.Target) : Prop :=
  S.regimeExt (targetToRegime S tg₁) (targetToRegime S tg₂)

def sameRow (S : SemanticSystem) (tg₁ tg₂ : S.Target) : Prop :=
  S.rowExt (targetToRow S tg₁) (targetToRow S tg₂)

def sameAtoms (S : SemanticSystem) (tg₁ tg₂ : S.Target) : Prop :=
  S.atomsExt (targetToAtoms S tg₁) (targetToAtoms S tg₂)

def sameShape (S : SemanticSystem) (tg₁ tg₂ : S.Target) : Prop :=
  S.shapeExt (targetToShape S tg₁) (targetToShape S tg₂)

end SemanticSystem

end Core
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
