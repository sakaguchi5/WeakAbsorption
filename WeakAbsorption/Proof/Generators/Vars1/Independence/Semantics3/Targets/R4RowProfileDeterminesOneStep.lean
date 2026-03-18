import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4PrimitiveCongruenceFailure

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core
open Necessity

theorem rowProfileProxyOfExactNode_eq_implies_oneStepExactNodes_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    oneStepExactNodes x = oneStepExactNodes y := by
  cases x with
  | core tg1 =>
      cases y with
      | core tg2 =>
          cases tg1 <;> cases tg2 <;>
            simp [rowProfileProxyOfExactNode, oneStepExactNodes] at h ⊢ <;>
            try cases h <;>
            rfl
      | leaf ℓ2 =>
          simp [rowProfileProxyOfExactNode] at h
  | leaf ℓ1 =>
      cases y with
      | core tg2 =>
          simp [rowProfileProxyOfExactNode] at h
      | leaf ℓ2 =>
          simp [rowProfileProxyOfExactNode] at h
          cases h
          rfl

theorem rowProfileProxyOfExactNode_eq_implies_oneStepSnapshotSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    oneStepSnapshotSignature x = oneStepSnapshotSignature y := by
  have hxy : oneStepExactNodes x = oneStepExactNodes y :=
    rowProfileProxyOfExactNode_eq_implies_oneStepExactNodes_eq h
  simpa [oneStepSnapshotSignature, oneStepSignatureWith] using
    congrArg (List.map snapshotProxyOfExactNode) hxy

theorem rowProfileProxyOfExactNode_eq_implies_oneStepCompressedSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    oneStepCompressedSignature x = oneStepCompressedSignature y := by
  have hxy : oneStepExactNodes x = oneStepExactNodes y :=
    rowProfileProxyOfExactNode_eq_implies_oneStepExactNodes_eq h
  simpa [oneStepCompressedSignature, oneStepSignatureWith] using
    congrArg (List.map compressedProxyOfExactNode) hxy

theorem rowProfileProxyOfExactNode_eq_implies_oneStepKernelShellRowProfileSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    oneStepKernelShellRowProfileSignature x =
      oneStepKernelShellRowProfileSignature y := by
  have hxy : oneStepExactNodes x = oneStepExactNodes y :=
    rowProfileProxyOfExactNode_eq_implies_oneStepExactNodes_eq h
  simpa [oneStepKernelShellRowProfileSignature, oneStepSignatureWith] using
    congrArg (List.map kernelShellRowProfileProxyOfExactNode) hxy

theorem rowProfileProxyOfExactNode_eq_implies_oneStepRowProfileSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    oneStepRowProfileSignature x = oneStepRowProfileSignature y := by
  have hxy : oneStepExactNodes x = oneStepExactNodes y :=
    rowProfileProxyOfExactNode_eq_implies_oneStepExactNodes_eq h
  simpa [oneStepRowProfileSignature, oneStepSignatureWith] using
    congrArg (List.map rowProfileProxyOfExactNode) hxy

theorem no_sameRowProfileDifferentCompressedOneStep
    {x y : ExactNode} :
    ¬ sameRowProfileDifferentCompressedOneStep x y := by
  intro h
  rcases h with ⟨hsrc, hneq⟩
  exact hneq (rowProfileProxyOfExactNode_eq_implies_oneStepCompressedSignature_eq hsrc)

theorem no_sameRowProfileDifferentKernelShellRowProfileOneStep
    {x y : ExactNode} :
    ¬ sameRowProfileDifferentKernelShellRowProfileOneStep x y := by
  intro h
  rcases h with ⟨hsrc, hneq⟩
  exact hneq
    (rowProfileProxyOfExactNode_eq_implies_oneStepKernelShellRowProfileSignature_eq hsrc)

theorem no_sameRowProfileDifferentSnapshotOneStep
    {x y : ExactNode} :
    ¬ sameRowProfileDifferentSnapshotOneStep x y := by
  intro h
  rcases h with ⟨hsrc, hneq⟩
  exact hneq (rowProfileProxyOfExactNode_eq_implies_oneStepSnapshotSignature_eq hsrc)

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
