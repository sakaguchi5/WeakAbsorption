import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Spine

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

section SemanticPackage

/--
Realized semantic states for the audited R4 core targets.
This keeps the shell-level information that is lost by kernel quotienting alone.
-/
inductive CoreRealizedState where
  | saRight
  | saLeftLift
  | decorRight_right
  | decorRight_leftLift
  | decorLeft_right
  | decorLeft_leftLift
  | stable_leftLift
  | hole_root
  | decorHole_root
  | aa_right
  | aa_leftLift
  | bridge_split
deriving DecidableEq, Repr

/-- Forgetful map from realized states back to the public target index. -/
def stateTarget : CoreRealizedState -> CoreKernelTarget
  | .saRight             => .nfXASqRightPred
  | .saLeftLift          => .nfUSqLiftRightSPred
  | .decorRight_right    => .nfXADecorRightPred
  | .decorRight_leftLift => .nfUDecorLiftRightSPred
  | .decorLeft_right     => .nfXADecorLeftPred
  | .decorLeft_leftLift  => .nfUDecorLiftLeftSPred
  | .stable_leftLift     => .nfUStablePred
  | .hole_root           => .nfUHolePred
  | .decorHole_root      => .nfUDecorHolePred
  | .aa_right            => .nfXASqAPred
  | .aa_leftLift         => .nfUSqLiftAPred
  | .bridge_split        => .nfUDecorRightPred

/-- The realized semantic state attached to a public core target. -/
def r4RealizedStateOf : CoreKernelTarget -> CoreRealizedState
  | .nfXASqRightPred        => .saRight
  | .nfUSqLiftRightSPred    => .saLeftLift
  | .nfXADecorRightPred     => .decorRight_right
  | .nfUDecorLiftRightSPred => .decorRight_leftLift
  | .nfXADecorLeftPred      => .decorLeft_right
  | .nfUDecorLiftLeftSPred  => .decorLeft_leftLift
  | .nfUStablePred          => .stable_leftLift
  | .nfUHolePred            => .hole_root
  | .nfUDecorHolePred       => .decorHole_root
  | .nfXASqAPred            => .aa_right
  | .nfUSqLiftAPred         => .aa_leftLift
  | .nfUDecorRightPred      => .bridge_split

theorem stateTarget_r4RealizedStateOf (tg : CoreKernelTarget) :
    stateTarget (r4RealizedStateOf tg) = tg := by
  cases tg <;> rfl

theorem r4RealizedStateOf_stateTarget (σ : CoreRealizedState) :
    r4RealizedStateOf (stateTarget σ) = σ := by
  cases σ <;> rfl

/--
The semantic package is the main proof object: one audited bundle per core target,
containing the kernel quotient, shell refinement, realized state, coarse regime,
and exact canonical row together with the already-proved certificates.
-/
structure R4SemanticPackage (tg : CoreKernelTarget) where
  kernel : CoreKernelClass
  shell  : CoreKernelShell
  state  : CoreRealizedState
  regime : CoreKernelRegime
  row    : PurifiedCtxRow

  audit      : KernelAuditClosed tg
  envelope   : TargetKernelEnvelope tg
  rowWitness : KernelRowRealized tg

  kernel_eq : kernel = coreKernelClass tg
  shell_eq  : shell = coreKernelShell tg
  state_eq  : state = r4RealizedStateOf tg
  regime_eq : regime = coreKernelRegime kernel
  row_eq    : row = corePurifiedRowOfTarget tg
  state_target : stateTarget state = tg

/-- Canonical semantic package for an audited R4 core target. -/
def r4SemanticPackageOf (tg : CoreKernelTarget) : R4SemanticPackage tg := by
  refine
    { kernel := coreKernelClass tg
      shell := coreKernelShell tg
      state := r4RealizedStateOf tg
      regime := coreKernelRegime (coreKernelClass tg)
      row := corePurifiedRowOfTarget tg
      audit := kernelAuditClosed_of_target tg
      envelope := targetKernelEnvelope_of_target tg
      rowWitness := kernelRowRealized_of_target tg
      kernel_eq := rfl
      shell_eq := rfl
      state_eq := rfl
      regime_eq := rfl
      row_eq := rfl
      state_target := stateTarget_r4RealizedStateOf tg }

/-- Package-level projection: the organic spine is already contained in the package. -/
def packageOrganicSpine (tg : CoreKernelTarget) : OrganicCoreSpine tg :=
  { audit := (r4SemanticPackageOf tg).audit
    envelope := (r4SemanticPackageOf tg).envelope
    row := (r4SemanticPackageOf tg).rowWitness }

/-- Package-level projection of the coarse regime semantics. -/
def packageRegime (tg : CoreKernelTarget) : CoreKernelRegime :=
  (r4SemanticPackageOf tg).regime

/-- Package-level projection of the exact row semantics. -/
def packageRow (tg : CoreKernelTarget) : PurifiedCtxRow :=
  (r4SemanticPackageOf tg).row

/-- Package-level projection of the realized state. -/
def packageState (tg : CoreKernelTarget) : CoreRealizedState :=
  (r4SemanticPackageOf tg).state

theorem package_kernel_eq (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).kernel = coreKernelClass tg :=
  (r4SemanticPackageOf tg).kernel_eq

theorem package_shell_eq (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).shell = coreKernelShell tg :=
  (r4SemanticPackageOf tg).shell_eq

theorem package_state_eq (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).state = r4RealizedStateOf tg :=
  (r4SemanticPackageOf tg).state_eq

theorem package_regime_eq (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).regime = coreKernelRegime (coreKernelClass tg) := by
  simpa [(r4SemanticPackageOf tg).kernel_eq] using
    (r4SemanticPackageOf tg).regime_eq

theorem package_row_eq (tg : CoreKernelTarget) :
    (r4SemanticPackageOf tg).row = corePurifiedRowOfTarget tg :=
  (r4SemanticPackageOf tg).row_eq

theorem package_state_target (tg : CoreKernelTarget) :
    stateTarget (packageState tg) = tg :=
  (r4SemanticPackageOf tg).state_target

theorem package_status_settled (tg : CoreKernelTarget) :
    coreKernelStatus ((r4SemanticPackageOf tg).kernel) = .settled := by
  simpa [package_kernel_eq tg] using coreKernelTarget_status tg

theorem package_codomain_settled (tg : CoreKernelTarget) :
    coreKernelCodomainStatus ((r4SemanticPackageOf tg).kernel) = .settled := by
  simpa [package_kernel_eq tg] using coreKernelTarget_codomainStatus tg

theorem package_support_exact (tg : CoreKernelTarget) :
    coreKernelSupportStatus ((r4SemanticPackageOf tg).kernel) = .exact := by
  simpa [package_kernel_eq tg] using coreKernelTarget_supportStatus tg

theorem package_audit (tg : CoreKernelTarget) :
    KernelAuditClosed tg :=
  (r4SemanticPackageOf tg).audit

theorem package_envelope (tg : CoreKernelTarget) :
    TargetKernelEnvelope tg :=
  (r4SemanticPackageOf tg).envelope

def packageRowWitness (tg : CoreKernelTarget) : KernelRowRealized tg :=
  (r4SemanticPackageOf tg).rowWitness

theorem package_bridgeSplit_iff_target_eq_nfUDecorRightPred
    (tg : CoreKernelTarget) :
    packageRegime tg = .bridgeSplit ↔ tg = .nfUDecorRightPred := by
  simpa [packageRegime, package_regime_eq tg] using
    bridgeSplit_iff_target_eq_nfUDecorRightPred tg

theorem package_pure_iff_target_ne_nfUDecorRightPred
    (tg : CoreKernelTarget) :
    packageRegime tg = .pure ↔ tg ≠ .nfUDecorRightPred := by
  simpa [packageRegime, package_regime_eq tg] using
    pure_iff_target_ne_nfUDecorRightPred tg

/-- The bridge-split target is exactly the unique bridge-split semantic package. -/
theorem package_state_bridgeSplit_iff_target_eq_nfUDecorRightPred
    (tg : CoreKernelTarget) :
    packageState tg = .bridge_split ↔ tg = .nfUDecorRightPred := by
  cases tg <;> simp [packageState, r4SemanticPackageOf, r4RealizedStateOf]

/-- Global bundled package data for all 12 core targets. -/
structure GlobalR4SemanticPackage where
  rootAudit : RootAuditClosed
  packageOf : ∀ tg : CoreKernelTarget, R4SemanticPackage tg

/-- Canonical global semantic package for the audited R4 core. -/
def globalR4SemanticPackage : GlobalR4SemanticPackage :=
  { rootAudit := rootAuditClosed
    packageOf := r4SemanticPackageOf }

end SemanticPackage

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
