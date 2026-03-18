import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4CompressedSnapshot
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_ExactNode

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core
open Necessity

/--
Turn the finite exact-child container into an ordered list.
This preserves multiplicity information if a future proxy collapses
distinct exact children to the same public proxy.
-/
def exactChildrenToList : ExactChildren → List ExactNode
  | .zero      => []
  | .one a     => [a]
  | .two a b   => [a, b]

@[simp] theorem exactChildrenToList_zero :
    exactChildrenToList .zero = [] := rfl

@[simp] theorem exactChildrenToList_one (a : ExactNode) :
    exactChildrenToList (.one a) = [a] := rfl

@[simp] theorem exactChildrenToList_two (a b : ExactNode) :
    exactChildrenToList (.two a b) = [a, b] := rfl

/-- Raw exact one-step children as a list. -/
def oneStepExactNodes (src : ExactNode) : List ExactNode :=
  exactChildrenToList (exactOneStepChildrenR4 src)

@[simp] theorem oneStepExactNodes_leaf_xa :
    oneStepExactNodes (.leaf .xa) = [.leaf .v] := rfl

@[simp] theorem oneStepExactNodes_leaf_u :
    oneStepExactNodes (.leaf .u) = [] := rfl

@[simp] theorem oneStepExactNodes_leaf_m :
    oneStepExactNodes (.leaf .m) = [] := rfl

@[simp] theorem oneStepExactNodes_leaf_v :
    oneStepExactNodes (.leaf .v) = [] := rfl

@[simp] theorem oneStepExactNodes_nfXASqRightPred :
    oneStepExactNodes (.core .nfXASqRightPred) = [.leaf .xa] := rfl

@[simp] theorem oneStepExactNodes_nfUSqLiftRightSPred :
    oneStepExactNodes (.core .nfUSqLiftRightSPred) = [.leaf .u] := rfl

@[simp] theorem oneStepExactNodes_nfXADecorRightPred :
    oneStepExactNodes (.core .nfXADecorRightPred) = [.leaf .xa] := rfl

@[simp] theorem oneStepExactNodes_nfUDecorLiftRightSPred :
    oneStepExactNodes (.core .nfUDecorLiftRightSPred) = [.leaf .u] := rfl

@[simp] theorem oneStepExactNodes_nfXADecorLeftPred :
    oneStepExactNodes (.core .nfXADecorLeftPred) = [.leaf .xa] := rfl

@[simp] theorem oneStepExactNodes_nfUDecorLiftLeftSPred :
    oneStepExactNodes (.core .nfUDecorLiftLeftSPred) = [.leaf .u] := rfl

@[simp] theorem oneStepExactNodes_nfUStablePred :
    oneStepExactNodes (.core .nfUStablePred) = [.leaf .u] := rfl

@[simp] theorem oneStepExactNodes_nfUHolePred :
    oneStepExactNodes (.core .nfUHolePred) = [.leaf .u] := rfl

@[simp] theorem oneStepExactNodes_nfUDecorHolePred :
    oneStepExactNodes (.core .nfUDecorHolePred) =
      [.leaf .u, .core .nfUHolePred] := rfl

@[simp] theorem oneStepExactNodes_nfXASqAPred :
    oneStepExactNodes (.core .nfXASqAPred) =
      [.leaf .xa, .core .nfXASqRightPred] := rfl

@[simp] theorem oneStepExactNodes_nfUSqLiftAPred :
    oneStepExactNodes (.core .nfUSqLiftAPred) =
      [.leaf .u, .core .nfUSqLiftRightSPred] := rfl

@[simp] theorem oneStepExactNodes_nfUDecorRightPred :
    oneStepExactNodes (.core .nfUDecorRightPred) =
      [.leaf .u, .leaf .m] := rfl

/--
A generic one-step signature obtained by pushing exact children through
any chosen proxy on `ExactNode`.
-/
def oneStepSignatureWith {α : Type _} (proxy : ExactNode → α) (src : ExactNode) : List α :=
  (oneStepExactNodes src).map proxy

/--
Most faithful currently available public proxy on Semantics3 side for exact nodes:
- core targets are read as full observed snapshots
- terminal exact leaves are kept explicitly as leaves
-/
abbrev SnapshotChildProxy :=
  Sum ExactLeaf ObservedKernelSnapshot

def snapshotProxyOfExactNode : ExactNode → SnapshotChildProxy
  | .core tg => .inr (observedSnapshot tg)
  | .leaf ℓ  => .inl ℓ

/--
Current audited compressed proxy:
- core targets are read as `(state, rowProfile)`
- leaves remain explicit
-/
abbrev CompressedChildProxy :=
  Sum ExactLeaf R4CompressedSnapshot

def compressedProxyOfExactNode : ExactNode → CompressedChildProxy
  | .core tg => .inr (compressedSnapshot tg)
  | .leaf ℓ  => .inl ℓ

/--
Readable candidate proxy for Final-style experiments:
- core targets are read as `(kernel, shell, rowProfile)`
- leaves remain explicit
-/
abbrev KernelShellRowProfileChildProxy :=
  Sum ExactLeaf (ObservedKernelClass × ObservedShellKind × ObservedRowProfile)

def kernelShellRowProfileProxyOfExactNode :
    ExactNode → KernelShellRowProfileChildProxy
  | .core tg => .inr (observedKernel tg, observedShell tg, observedRowProfile tg)
  | .leaf ℓ  => .inl ℓ

/--
Pure geometry-side proxy:
- core targets are read only by `rowProfile`
- leaves remain explicit
-/
abbrev RowProfileChildProxy :=
  Sum ExactLeaf ObservedRowProfile

def rowProfileProxyOfExactNode : ExactNode → RowProfileChildProxy
  | .core tg => .inr (observedRowProfile tg)
  | .leaf ℓ  => .inl ℓ

/-- Full snapshot-level one-step proxy signature. -/
def oneStepSnapshotSignature (src : ExactNode) : List SnapshotChildProxy :=
  oneStepSignatureWith snapshotProxyOfExactNode src

/-- Compressed `(state,rowProfile)` one-step proxy signature. -/
def oneStepCompressedSignature (src : ExactNode) : List CompressedChildProxy :=
  oneStepSignatureWith compressedProxyOfExactNode src

/-- `(kernel,shell,rowProfile)` one-step proxy signature. -/
def oneStepKernelShellRowProfileSignature
    (src : ExactNode) : List KernelShellRowProfileChildProxy :=
  oneStepSignatureWith kernelShellRowProfileProxyOfExactNode src

/-- `rowProfile`-only one-step proxy signature. -/
def oneStepRowProfileSignature (src : ExactNode) : List RowProfileChildProxy :=
  oneStepSignatureWith rowProfileProxyOfExactNode src

@[simp] theorem snapshotProxyOfExactNode_core (tg : ObservedTarget) :
    snapshotProxyOfExactNode (.core tg) = .inr (observedSnapshot tg) := rfl

@[simp] theorem snapshotProxyOfExactNode_leaf (ℓ : ExactLeaf) :
    snapshotProxyOfExactNode (.leaf ℓ) = .inl ℓ := rfl

@[simp] theorem compressedProxyOfExactNode_core (tg : ObservedTarget) :
    compressedProxyOfExactNode (.core tg) = .inr (compressedSnapshot tg) := rfl

@[simp] theorem compressedProxyOfExactNode_leaf (ℓ : ExactLeaf) :
    compressedProxyOfExactNode (.leaf ℓ) = .inl ℓ := rfl

@[simp] theorem kernelShellRowProfileProxyOfExactNode_core (tg : ObservedTarget) :
    kernelShellRowProfileProxyOfExactNode (.core tg) =
      .inr (observedKernel tg, observedShell tg, observedRowProfile tg) := rfl

@[simp] theorem kernelShellRowProfileProxyOfExactNode_leaf (ℓ : ExactLeaf) :
    kernelShellRowProfileProxyOfExactNode (.leaf ℓ) = .inl ℓ := rfl

@[simp] theorem rowProfileProxyOfExactNode_core (tg : ObservedTarget) :
    rowProfileProxyOfExactNode (.core tg) = .inr (observedRowProfile tg) := rfl

@[simp] theorem rowProfileProxyOfExactNode_leaf (ℓ : ExactLeaf) :
    rowProfileProxyOfExactNode (.leaf ℓ) = .inl ℓ := rfl

@[simp] theorem oneStepSnapshotSignature_leaf_xa :
    oneStepSnapshotSignature (.leaf .xa) = [.inl .v] := rfl

@[simp] theorem oneStepSnapshotSignature_leaf_u :
    oneStepSnapshotSignature (.leaf .u) = [] := rfl

@[simp] theorem oneStepSnapshotSignature_leaf_m :
    oneStepSnapshotSignature (.leaf .m) = [] := rfl

@[simp] theorem oneStepSnapshotSignature_leaf_v :
    oneStepSnapshotSignature (.leaf .v) = [] := rfl

@[simp] theorem oneStepSnapshotSignature_nfUDecorHolePred :
    oneStepSnapshotSignature (.core .nfUDecorHolePred) =
      [ .inl .u
      , .inr (observedSnapshot .nfUHolePred)
      ] := rfl

@[simp] theorem oneStepSnapshotSignature_nfXASqAPred :
    oneStepSnapshotSignature (.core .nfXASqAPred) =
      [ .inl .xa
      , .inr (observedSnapshot .nfXASqRightPred)
      ] := rfl

@[simp] theorem oneStepSnapshotSignature_nfUSqLiftAPred :
    oneStepSnapshotSignature (.core .nfUSqLiftAPred) =
      [ .inl .u
      , .inr (observedSnapshot .nfUSqLiftRightSPred)
      ] := rfl

@[simp] theorem oneStepSnapshotSignature_nfUDecorRightPred :
    oneStepSnapshotSignature (.core .nfUDecorRightPred) =
      [ .inl .u
      , .inl .m
      ] := rfl

@[simp] theorem oneStepCompressedSignature_nfUDecorHolePred :
    oneStepCompressedSignature (.core .nfUDecorHolePred) =
      [ .inl .u
      , .inr (compressedSnapshot .nfUHolePred)
      ] := rfl

@[simp] theorem oneStepCompressedSignature_nfXASqAPred :
    oneStepCompressedSignature (.core .nfXASqAPred) =
      [ .inl .xa
      , .inr (compressedSnapshot .nfXASqRightPred)
      ] := rfl

@[simp] theorem oneStepCompressedSignature_nfUSqLiftAPred :
    oneStepCompressedSignature (.core .nfUSqLiftAPred) =
      [ .inl .u
      , .inr (compressedSnapshot .nfUSqLiftRightSPred)
      ] := rfl

@[simp] theorem oneStepCompressedSignature_nfUDecorRightPred :
    oneStepCompressedSignature (.core .nfUDecorRightPred) =
      [ .inl .u
      , .inl .m
      ] := rfl

@[simp] theorem oneStepKernelShellRowProfileSignature_nfUDecorHolePred :
    oneStepKernelShellRowProfileSignature (.core .nfUDecorHolePred) =
      [ .inl .u
      , .inr
          ( observedKernel .nfUHolePred
          , observedShell .nfUHolePred
          , observedRowProfile .nfUHolePred )
      ] := rfl

@[simp] theorem oneStepKernelShellRowProfileSignature_nfXASqAPred :
    oneStepKernelShellRowProfileSignature (.core .nfXASqAPred) =
      [ .inl .xa
      , .inr
          ( observedKernel .nfXASqRightPred
          , observedShell .nfXASqRightPred
          , observedRowProfile .nfXASqRightPred )
      ] := rfl

@[simp] theorem oneStepKernelShellRowProfileSignature_nfUSqLiftAPred :
    oneStepKernelShellRowProfileSignature (.core .nfUSqLiftAPred) =
      [ .inl .u
      , .inr
          ( observedKernel .nfUSqLiftRightSPred
          , observedShell .nfUSqLiftRightSPred
          , observedRowProfile .nfUSqLiftRightSPred )
      ] := rfl

@[simp] theorem oneStepKernelShellRowProfileSignature_nfUDecorRightPred :
    oneStepKernelShellRowProfileSignature (.core .nfUDecorRightPred) =
      [ .inl .u
      , .inl .m
      ] := rfl

@[simp] theorem oneStepRowProfileSignature_nfUDecorHolePred :
    oneStepRowProfileSignature (.core .nfUDecorHolePred) =
      [ .inl .u
      , .inr (observedRowProfile .nfUHolePred)
      ] := rfl

@[simp] theorem oneStepRowProfileSignature_nfXASqAPred :
    oneStepRowProfileSignature (.core .nfXASqAPred) =
      [ .inl .xa
      , .inr (observedRowProfile .nfXASqRightPred)
      ] := rfl

@[simp] theorem oneStepRowProfileSignature_nfUSqLiftAPred :
    oneStepRowProfileSignature (.core .nfUSqLiftAPred) =
      [ .inl .u
      , .inr (observedRowProfile .nfUSqLiftRightSPred)
      ] := rfl

@[simp] theorem oneStepRowProfileSignature_nfUDecorRightPred :
    oneStepRowProfileSignature (.core .nfUDecorRightPred) =
      [ .inl .u
      , .inl .m
      ] := rfl

/--
Convenient predicate for the next file:
same chosen source proxy, but different one-step proxy signature.
-/
def SameSourceProxyDifferentOneStep
    {α β : Type _}
    (srcProxy : ExactNode → α)
    (childProxy : ExactNode → β)
    (x y : ExactNode) : Prop :=
  srcProxy x = srcProxy y
    ∧ oneStepSignatureWith childProxy x ≠ oneStepSignatureWith childProxy y

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
