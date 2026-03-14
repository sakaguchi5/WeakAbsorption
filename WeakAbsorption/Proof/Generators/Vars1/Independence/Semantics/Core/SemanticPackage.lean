import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Core.SemanticSystem

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics
namespace Core

open SemanticSystem

structure SemanticPackage (S : SemanticSystem) (tg : S.Target) where
  state  : S.State
  kernel : S.Kernel
  shell  : S.Shell
  regime : S.Regime
  row    : S.Row
  atoms  : List S.Atom
  shape  : List S.Shape

  state_eq  : state = S.targetToState tg
  kernel_eq : kernel = S.stateToKernel state
  shell_eq  : shell = S.stateToShell state
  regime_eq : regime = S.stateToRegime state
  row_eq    : row = S.stateToRow state
  atoms_eq  : atoms = S.rowToAtoms row
  shape_eq  : shape = S.atomsToShape atoms

def canonicalPackage (S : SemanticSystem) (tg : S.Target) : SemanticPackage S tg :=
  { state := S.targetToState tg
    kernel := S.stateToKernel (S.targetToState tg)
    shell := S.stateToShell (S.targetToState tg)
    regime := S.stateToRegime (S.targetToState tg)
    row := S.stateToRow (S.targetToState tg)
    atoms := S.rowToAtoms (S.stateToRow (S.targetToState tg))
    shape := S.atomsToShape (S.rowToAtoms (S.stateToRow (S.targetToState tg)))
    state_eq := rfl
    kernel_eq := rfl
    shell_eq := rfl
    regime_eq := rfl
    row_eq := rfl
    atoms_eq := rfl
    shape_eq := rfl }

end Core
end Semantics
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
