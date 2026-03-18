import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4OneStepProxySignature
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4FinalReadiness


namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core
open Necessity

theorem snapshotProxyOfExactNode_injective :
    Function.Injective snapshotProxyOfExactNode := by
  intro x y h
  cases x with
  | core tg1 =>
      cases y with
      | core tg2 =>
          simp [snapshotProxyOfExactNode] at h
          exact congrArg ExactNode.core (observedSnapshot_injective h)
      | leaf ℓ2 =>
          simp [snapshotProxyOfExactNode] at h
  | leaf ℓ1 =>
      cases y with
      | core tg2 =>
          simp [snapshotProxyOfExactNode] at h
      | leaf ℓ2 =>
          simp [snapshotProxyOfExactNode] at h
          exact congrArg ExactNode.leaf h

theorem compressedProxyOfExactNode_injective :
    Function.Injective compressedProxyOfExactNode := by
  intro x y h
  cases x with
  | core tg1 =>
      cases y with
      | core tg2 =>
          simp [compressedProxyOfExactNode] at h
          exact congrArg ExactNode.core (compressedSnapshot_injective h)
      | leaf ℓ2 =>
          simp [compressedProxyOfExactNode] at h
  | leaf ℓ1 =>
      cases y with
      | core tg2 =>
          simp [compressedProxyOfExactNode] at h
      | leaf ℓ2 =>
          simp [compressedProxyOfExactNode] at h
          exact congrArg ExactNode.leaf h

theorem kernelShellRowProfileProxyOfExactNode_injective :
    Function.Injective kernelShellRowProfileProxyOfExactNode := by
  intro x y h
  cases x with
  | core tg1 =>
      cases y with
      | core tg2 =>
          simp [kernelShellRowProfileProxyOfExactNode] at h
          rcases h with ⟨hk, hs, hp⟩
          have hks : observedKernelShell tg1 = observedKernelShell tg2 :=
            Prod.ext hk hs
          exact congrArg ExactNode.core
            (kernelShell_and_rowProfile_determine_target hks hp)
      | leaf ℓ2 =>
          simp [kernelShellRowProfileProxyOfExactNode] at h
  | leaf ℓ1 =>
      cases y with
      | core tg2 =>
          simp [kernelShellRowProfileProxyOfExactNode] at h
      | leaf ℓ2 =>
          simp [kernelShellRowProfileProxyOfExactNode] at h
          exact congrArg ExactNode.leaf h

theorem rowProfileProxyOfExactNode_not_injective :
    ¬ Function.Injective rowProfileProxyOfExactNode := by
  intro hinj
  have hEq :
      rowProfileProxyOfExactNode (.core .nfXADecorRightPred) =
        rowProfileProxyOfExactNode (.core .nfXADecorLeftPred) := by
    simp [rowProfileProxyOfExactNode]
    native_decide
  have hne :
      (.core .nfXADecorRightPred : ExactNode) ≠
        (.core .nfXADecorLeftPred : ExactNode) := by
    decide
  exact hne (hinj hEq)

theorem no_sameSourceProxyDifferentOneStep_of_injective
    {α β : Type _}
    {srcProxy : ExactNode → α}
    {childProxy : ExactNode → β}
    (hinj : Function.Injective srcProxy)
    {x y : ExactNode} :
    ¬ SameSourceProxyDifferentOneStep srcProxy childProxy x y := by
  intro h
  rcases h with ⟨hxy, hneq⟩
  have hx : x = y := hinj hxy
  subst hx
  exact hneq rfl

theorem no_sameSnapshotProxyDifferentOneStep
    {x y : ExactNode} :
    ¬ SameSourceProxyDifferentOneStep
        snapshotProxyOfExactNode
        snapshotProxyOfExactNode
        x y :=
  no_sameSourceProxyDifferentOneStep_of_injective
    snapshotProxyOfExactNode_injective

theorem no_sameCompressedProxyDifferentOneStep
    {x y : ExactNode} :
    ¬ SameSourceProxyDifferentOneStep
        compressedProxyOfExactNode
        compressedProxyOfExactNode
        x y :=
  no_sameSourceProxyDifferentOneStep_of_injective
    compressedProxyOfExactNode_injective

theorem no_sameKernelShellRowProfileProxyDifferentOneStep
    {x y : ExactNode} :
    ¬ SameSourceProxyDifferentOneStep
        kernelShellRowProfileProxyOfExactNode
        kernelShellRowProfileProxyOfExactNode
        x y :=
  no_sameSourceProxyDifferentOneStep_of_injective
    kernelShellRowProfileProxyOfExactNode_injective

theorem rowProfile_sameSource_pair_exists :
    ∃ x y : ExactNode,
      x ≠ y ∧
      rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y := by
  refine ⟨.core .nfXADecorRightPred, .core .nfXADecorLeftPred, ?_, ?_⟩
  · decide
  · simp [rowProfileProxyOfExactNode]
    native_decide

theorem rowProfile_sameSource_sameOneStep_example :
    rowProfileProxyOfExactNode (.core .nfXADecorRightPred) =
      rowProfileProxyOfExactNode (.core .nfXADecorLeftPred)
    ∧
    oneStepRowProfileSignature (.core .nfXADecorRightPred) =
      oneStepRowProfileSignature (.core .nfXADecorLeftPred) := by
  constructor
  · simp [rowProfileProxyOfExactNode]
    native_decide
  ·
    simp [oneStepRowProfileSignature, oneStepSignatureWith,
      oneStepExactNodes_nfXADecorRightPred, oneStepExactNodes_nfXADecorLeftPred,
      rowProfileProxyOfExactNode]

def allExactNodes : List ExactNode :=
  [ .core .nfXASqRightPred
  , .core .nfUSqLiftRightSPred
  , .core .nfXADecorRightPred
  , .core .nfUDecorLiftRightSPred
  , .core .nfXADecorLeftPred
  , .core .nfUDecorLiftLeftSPred
  , .core .nfUStablePred
  , .core .nfUHolePred
  , .core .nfUDecorHolePred
  , .core .nfXASqAPred
  , .core .nfUSqLiftAPred
  , .core .nfUDecorRightPred
  , .leaf .xa
  , .leaf .u
  , .leaf .m
  , .leaf .v
  ]

def sameRowProfileDifferentCompressedOneStep (x y : ExactNode) : Prop :=
  SameSourceProxyDifferentOneStep
    rowProfileProxyOfExactNode
    compressedProxyOfExactNode
    x y

def sameRowProfileDifferentKernelShellRowProfileOneStep
    (x y : ExactNode) : Prop :=
  SameSourceProxyDifferentOneStep
    rowProfileProxyOfExactNode
    kernelShellRowProfileProxyOfExactNode
    x y

def sameRowProfileDifferentSnapshotOneStep (x y : ExactNode) : Prop :=
  SameSourceProxyDifferentOneStep
    rowProfileProxyOfExactNode
    snapshotProxyOfExactNode
    x y

def findPairInList
    (p : ExactNode → ExactNode → Prop)
    [DecidableEq ExactNode]
    [∀ x y, Decidable (p x y)] :
    List ExactNode → List ExactNode → Option (ExactNode × ExactNode)
  | [], _ => none
  | x :: xs, ys =>
      match ys.find? (fun y => decide (p x y)) with
      | some y => some (x, y)
      | none   => findPairInList p xs ys

def findExactPair
    (p : ExactNode → ExactNode → Prop)
    [DecidableEq ExactNode]
    [∀ x y, Decidable (p x y)] :
    Option (ExactNode × ExactNode) :=
  findPairInList p allExactNodes allExactNodes

def sameRowProfileDifferentCompressedOneStepB (x y : ExactNode) : Bool :=
  decide (rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) &&
    !(decide (oneStepCompressedSignature x = oneStepCompressedSignature y))

def sameRowProfileDifferentKernelShellRowProfileOneStepB
    (x y : ExactNode) : Bool :=
  decide (rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) &&
    !(decide
      (oneStepKernelShellRowProfileSignature x =
        oneStepKernelShellRowProfileSignature y))

def sameRowProfileDifferentSnapshotOneStepB
    (x y : ExactNode) : Bool :=
  decide (rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) &&
    !(decide (oneStepSnapshotSignature x = oneStepSnapshotSignature y))

def findInListB (p : α → Bool) : List α → Option α
  | [] => none
  | a :: as => if p a then some a else findInListB p as

def findPairInListB
    (p : ExactNode → ExactNode → Bool) :
    List ExactNode → List ExactNode → Option (ExactNode × ExactNode)
  | [], _ => none
  | x :: xs, ys =>
      match findInListB (fun y => p x y) ys with
      | some y => some (x, y)
      | none   => findPairInListB p xs ys

def findExactPairB
    (p : ExactNode → ExactNode → Bool) :
    Option (ExactNode × ExactNode) :=
  findPairInListB p allExactNodes allExactNodes

#eval findExactPairB sameRowProfileDifferentCompressedOneStepB
#eval findExactPairB sameRowProfileDifferentKernelShellRowProfileOneStepB
#eval findExactPairB sameRowProfileDifferentSnapshotOneStepB



end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
