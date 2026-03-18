import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.R4RowProfileDeterminesOneStep

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Targets

open Core
open Necessity

def listBind (xs : List α) (f : α → List β) : List β :=
  match xs with
  | [] => []
  | x :: xs => f x ++ listBind xs f

@[simp] theorem listBind_nil (f : α → List β) :
    listBind ([] : List α) f = [] := rfl

@[simp] theorem listBind_cons (x : α) (xs : List α) (f : α → List β) :
    listBind (x :: xs) f = f x ++ listBind xs f := rfl

/--
`futureExactNodes n x` = nodes reachable from `x`
after one step and then `n` further rounds of expansion.
-/
def futureExactNodes : Nat → ExactNode → List ExactNode
  | 0, x => oneStepExactNodes x
  | n + 1, x => listBind (futureExactNodes n x) oneStepExactNodes

def futureSignatureWith {α : Type _}
    (proxy : ExactNode → α) (n : Nat) (src : ExactNode) : List α :=
  (futureExactNodes n src).map proxy

def futureSnapshotSignature (n : Nat) (src : ExactNode) : List SnapshotChildProxy :=
  futureSignatureWith snapshotProxyOfExactNode n src

def futureCompressedSignature (n : Nat) (src : ExactNode) : List CompressedChildProxy :=
  futureSignatureWith compressedProxyOfExactNode n src

def futureKernelShellRowProfileSignature
    (n : Nat) (src : ExactNode) : List KernelShellRowProfileChildProxy :=
  futureSignatureWith kernelShellRowProfileProxyOfExactNode n src

def futureRowProfileSignature
    (n : Nat) (src : ExactNode) : List RowProfileChildProxy :=
  futureSignatureWith rowProfileProxyOfExactNode n src

@[simp] theorem futureExactNodes_zero (x : ExactNode) :
    futureExactNodes 0 x = oneStepExactNodes x := rfl

@[simp] theorem futureExactNodes_succ (n : Nat) (x : ExactNode) :
    futureExactNodes (n + 1) x = listBind (futureExactNodes n x) oneStepExactNodes := rfl

theorem rowProfileProxyOfExactNode_eq_implies_futureExactNodes_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    ∀ n, futureExactNodes n x = futureExactNodes n y := by
  intro n
  induction n with
  | zero =>
      exact rowProfileProxyOfExactNode_eq_implies_oneStepExactNodes_eq h
  | succ n ih =>
      simpa [futureExactNodes] using
        congrArg (fun zs => listBind zs oneStepExactNodes) ih

theorem rowProfileProxyOfExactNode_eq_implies_futureSnapshotSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    ∀ n, futureSnapshotSignature n x = futureSnapshotSignature n y := by
  intro n
  have hxy : futureExactNodes n x = futureExactNodes n y :=
    rowProfileProxyOfExactNode_eq_implies_futureExactNodes_eq h n
  simpa [futureSnapshotSignature, futureSignatureWith] using
    congrArg (List.map snapshotProxyOfExactNode) hxy

theorem rowProfileProxyOfExactNode_eq_implies_futureCompressedSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    ∀ n, futureCompressedSignature n x = futureCompressedSignature n y := by
  intro n
  have hxy : futureExactNodes n x = futureExactNodes n y :=
    rowProfileProxyOfExactNode_eq_implies_futureExactNodes_eq h n
  simpa [futureCompressedSignature, futureSignatureWith] using
    congrArg (List.map compressedProxyOfExactNode) hxy

theorem rowProfileProxyOfExactNode_eq_implies_futureKernelShellRowProfileSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    ∀ n,
      futureKernelShellRowProfileSignature n x =
        futureKernelShellRowProfileSignature n y := by
  intro n
  have hxy : futureExactNodes n x = futureExactNodes n y :=
    rowProfileProxyOfExactNode_eq_implies_futureExactNodes_eq h n
  simpa [futureKernelShellRowProfileSignature, futureSignatureWith] using
    congrArg (List.map kernelShellRowProfileProxyOfExactNode) hxy

theorem rowProfileProxyOfExactNode_eq_implies_futureRowProfileSignature_eq
    {x y : ExactNode}
    (h : rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y) :
    ∀ n, futureRowProfileSignature n x = futureRowProfileSignature n y := by
  intro n
  have hxy : futureExactNodes n x = futureExactNodes n y :=
    rowProfileProxyOfExactNode_eq_implies_futureExactNodes_eq h n
  simpa [futureRowProfileSignature, futureSignatureWith] using
    congrArg (List.map rowProfileProxyOfExactNode) hxy

def sameRowProfileDifferentFutureCompressedSignature
    (n : Nat) (x y : ExactNode) : Prop :=
  rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y ∧
    futureCompressedSignature n x ≠ futureCompressedSignature n y

def sameRowProfileDifferentFutureKernelShellRowProfileSignature
    (n : Nat) (x y : ExactNode) : Prop :=
  rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y ∧
    futureKernelShellRowProfileSignature n x ≠
      futureKernelShellRowProfileSignature n y

def sameRowProfileDifferentFutureSnapshotSignature
    (n : Nat) (x y : ExactNode) : Prop :=
  rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y ∧
    futureSnapshotSignature n x ≠ futureSnapshotSignature n y

def sameRowProfileDifferentFutureRowProfileSignature
    (n : Nat) (x y : ExactNode) : Prop :=
  rowProfileProxyOfExactNode x = rowProfileProxyOfExactNode y ∧
    futureRowProfileSignature n x ≠ futureRowProfileSignature n y

theorem no_sameRowProfileDifferentFutureCompressedSignature
    (n : Nat) {x y : ExactNode} :
    ¬ sameRowProfileDifferentFutureCompressedSignature n x y := by
  intro h
  rcases h with ⟨hsrc, hneq⟩
  exact hneq
    (rowProfileProxyOfExactNode_eq_implies_futureCompressedSignature_eq hsrc n)

theorem no_sameRowProfileDifferentFutureKernelShellRowProfileSignature
    (n : Nat) {x y : ExactNode} :
    ¬ sameRowProfileDifferentFutureKernelShellRowProfileSignature n x y := by
  intro h
  rcases h with ⟨hsrc, hneq⟩
  exact hneq
    (rowProfileProxyOfExactNode_eq_implies_futureKernelShellRowProfileSignature_eq hsrc n)

theorem no_sameRowProfileDifferentFutureSnapshotSignature
    (n : Nat) {x y : ExactNode} :
    ¬ sameRowProfileDifferentFutureSnapshotSignature n x y := by
  intro h
  rcases h with ⟨hsrc, hneq⟩
  exact hneq
    (rowProfileProxyOfExactNode_eq_implies_futureSnapshotSignature_eq hsrc n)

theorem no_sameRowProfileDifferentFutureRowProfileSignature
    (n : Nat) {x y : ExactNode} :
    ¬ sameRowProfileDifferentFutureRowProfileSignature n x y := by
  intro h
  rcases h with ⟨hsrc, hneq⟩
  exact hneq
    (rowProfileProxyOfExactNode_eq_implies_futureRowProfileSignature_eq hsrc n)

end Targets
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
