import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Targets

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

inductive CoreKernelClass where
  | saKernel
  | decorRightKernel
  | decorLeftKernel
  | aaKernel
  | stableKernel
  | holeKernel
  | decorHoleKernel
  | bridgeKernel
deriving DecidableEq, Repr

/--
Legacy coarse status retained for compatibility with the earlier Stage 5/6 code.
It is intentionally weaker than the audited semantic statuses introduced below.
-/
inductive CoreKernelStatus where
  | settled
  | pending
deriving DecidableEq, Repr

/-- Whether the set of possible codomain exits is already fixed. -/
inductive CoreKernelCodomainStatus where
  | unsettled
  | settled
deriving DecidableEq, Repr

/-- How much exact support auditing has actually been completed. -/
inductive CoreKernelSupportStatus where
  | unaudited
  | partial_
  | exact
deriving DecidableEq, Repr

/-- Whether the kernel belongs to the pure regime or to the bridge-split regime. -/
inductive CoreKernelRegime where
  | pure
  | bridgeSplit
deriving DecidableEq, Repr



inductive CoreKernelShell where
  | rightShell
  | leftLift
  | rootShell
  | bridgeSplitShell
 deriving DecidableEq, Repr

/--
Lightweight registry payload for a kernel target: the class, shell role, and audited statuses.
This is intentionally smaller than the earlier row-by-row registries.
-/
structure CoreKernelView where
  cls            : CoreKernelClass
  shell          : CoreKernelShell
  codomainStatus : CoreKernelCodomainStatus
  supportStatus  : CoreKernelSupportStatus
  regime         : CoreKernelRegime
 deriving Repr

inductive CoreKernelTarget where
  | nfXASqRightPred
  | nfUSqLiftRightSPred
  | nfXADecorRightPred
  | nfUDecorLiftRightSPred
  | nfXADecorLeftPred
  | nfUDecorLiftLeftSPred
  | nfUStablePred
  | nfUHolePred
  | nfUDecorHolePred
  | nfXASqAPred
  | nfUSqLiftAPred
  | nfUDecorRightPred
deriving DecidableEq, Repr

def coreKernelClass : CoreKernelTarget -> CoreKernelClass
  | .nfXASqRightPred => .saKernel
  | .nfUSqLiftRightSPred => .saKernel
  | .nfXADecorRightPred => .decorRightKernel
  | .nfUDecorLiftRightSPred => .decorRightKernel
  | .nfXADecorLeftPred => .decorLeftKernel
  | .nfUDecorLiftLeftSPred => .decorLeftKernel
  | .nfUStablePred => .stableKernel
  | .nfUHolePred => .holeKernel
  | .nfUDecorHolePred => .decorHoleKernel
  | .nfXASqAPred => .aaKernel
  | .nfUSqLiftAPred => .aaKernel
  | .nfUDecorRightPred => .bridgeKernel



def coreKernelShell : CoreKernelTarget -> CoreKernelShell
  | .nfXASqRightPred => .rightShell
  | .nfUSqLiftRightSPred => .leftLift
  | .nfXADecorRightPred => .rightShell
  | .nfUDecorLiftRightSPred => .leftLift
  | .nfXADecorLeftPred => .rightShell
  | .nfUDecorLiftLeftSPred => .leftLift
  | .nfUStablePred => .leftLift
  | .nfUHolePred => .rootShell
  | .nfUDecorHolePred => .rootShell
  | .nfXASqAPred => .rightShell
  | .nfUSqLiftAPred => .leftLift
  | .nfUDecorRightPred => .bridgeSplitShell

def coreKernelStatus : CoreKernelClass -> CoreKernelStatus
  | .saKernel => .settled
  | .decorRightKernel => .settled
  | .decorLeftKernel => .settled
  | .aaKernel => .settled
  | .stableKernel => .settled
  | .holeKernel => .settled
  | .decorHoleKernel => .settled
  | .bridgeKernel => .settled

/-- Audited semantic codomain status: after the current re-audit, every kernel class has
its codomain geometry fixed, even when exact support is still only partial. -/
def coreKernelCodomainStatus : CoreKernelClass -> CoreKernelCodomainStatus
  | .saKernel => .settled
  | .decorRightKernel => .settled
  | .decorLeftKernel => .settled
  | .aaKernel => .settled
  | .stableKernel => .settled
  | .holeKernel => .settled
  | .decorHoleKernel => .settled
  | .bridgeKernel => .settled

/-- Audited semantic support status: this records whether the exact empty/singleton/branching
shape has really been certified, not merely proposed by a provisional row. -/
def coreKernelSupportStatus : CoreKernelClass -> CoreKernelSupportStatus
  | .saKernel => .exact
  | .decorRightKernel => .exact
  | .decorLeftKernel => .exact
  | .aaKernel => .exact
  | .stableKernel => .exact
  | .holeKernel => .exact
  | .decorHoleKernel => .exact
  | .bridgeKernel => .exact

/-- Audited semantic regime. The bridge kernel is the unique bridge-split class. -/
def coreKernelRegime : CoreKernelClass -> CoreKernelRegime
  | .bridgeKernel => .bridgeSplit
  | _ => .pure



def coreKernelView (tg : CoreKernelTarget) : CoreKernelView :=
  { cls := coreKernelClass tg
    shell := coreKernelShell tg
    codomainStatus := coreKernelCodomainStatus (coreKernelClass tg)
    supportStatus := coreKernelSupportStatus (coreKernelClass tg)
    regime := coreKernelRegime (coreKernelClass tg) }

/-- Every target already sits in its lightweight kernel view with settled semantics. -/
theorem coreKernelView_semantics
    (tg : CoreKernelTarget) :
    (coreKernelView tg).cls = coreKernelClass tg ∧
    (coreKernelView tg).shell = coreKernelShell tg ∧
    (coreKernelView tg).codomainStatus = .settled ∧
    (coreKernelView tg).supportStatus = .exact ∧
    (coreKernelView tg).regime =
      match tg with
      | .nfUDecorRightPred => .bridgeSplit
      | _ => .pure := by
  cases tg <;>
    simp [coreKernelView, coreKernelClass, coreKernelShell,
      coreKernelCodomainStatus, coreKernelSupportStatus, coreKernelRegime]

theorem coreKernelTarget_status
    (tg : CoreKernelTarget) :
    coreKernelStatus (coreKernelClass tg) = .settled := by
  cases tg <;> rfl


theorem coreKernelTarget_codomainStatus
    (tg : CoreKernelTarget) :
    coreKernelCodomainStatus (coreKernelClass tg) = .settled := by
  cases tg <;> rfl

theorem coreKernelTarget_supportStatus
    (tg : CoreKernelTarget) :
    coreKernelSupportStatus (coreKernelClass tg) = .exact := by
  cases tg <;> rfl

theorem coreKernelTarget_regime
    (tg : CoreKernelTarget) :
    coreKernelRegime (coreKernelClass tg) =
      match tg with
      | .nfUDecorRightPred => .bridgeSplit
      | _ => .pure := by
  cases tg <;> rfl

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
