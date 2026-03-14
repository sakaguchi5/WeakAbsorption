import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RowsBridge
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Family

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

section OrganicSpine

/-!
This file is intentionally thin.
It does not refactor the lower files yet; it only exposes the already-proved story
as a single top-down spine:

  root-local audit
    -> kernel classification / exactness
    -> canonical purified row realization
    -> pure / bridge-split family interpretation
-/

/- =========================================================
   1. root / plug audit closure
   ========================================================= -/

structure RootAuditClosed where
  root  : ∀ tg : RootTarget, TargetRowCertificate tg
  lhs   : ∀ tg : PlugMainTarget, PlugLhsRowCertificate tg
  rhs   : ∀ tg : PlugRhsTarget, PlugRhsRowCertificate tg

def rootAuditClosed : RootAuditClosed := {
  root := rootRowCertificate
  lhs := plugLhsRowCertificate
  rhs := plugRhsRowCertificate
}

def root_target_audited (tg : RootTarget) :
    TargetRowCertificate tg :=
  rootAuditClosed.root tg

def plug_lhs_target_audited (tg : PlugMainTarget) :
    PlugLhsRowCertificate tg :=
  rootAuditClosed.lhs tg

def plug_rhs_target_audited (tg : PlugRhsTarget) :
    PlugRhsRowCertificate tg :=
  rootAuditClosed.rhs tg

/- =========================================================
   2. target -> kernel view closure
   ========================================================= -/

def KernelAuditClosed (tg : CoreKernelTarget) : Prop :=
  (coreKernelView tg).cls = coreKernelClass tg ∧
  (coreKernelView tg).shell = coreKernelShell tg ∧
  coreKernelStatus (coreKernelClass tg) = .settled ∧
  coreKernelCodomainStatus (coreKernelClass tg) = .settled ∧
  coreKernelSupportStatus (coreKernelClass tg) = .exact ∧
  coreKernelRegime (coreKernelClass tg) =
    match tg with
    | .nfUDecorRightPred => .bridgeSplit
    | _ => .pure

theorem kernelAuditClosed_of_target (tg : CoreKernelTarget) :
    KernelAuditClosed tg := by
  rcases coreKernelView_semantics tg with
    ⟨hcls, hshell, hcod, hsupp, hreg⟩
  exact ⟨hcls, hshell,
    coreKernelTarget_status tg,
    coreKernelTarget_codomainStatus tg,
    coreKernelTarget_supportStatus tg,
    coreKernelTarget_regime tg⟩

/- =========================================================
   3. kernel semantics in target-indexed form
   ========================================================= -/

def TargetKernelEnvelope : CoreKernelTarget -> Prop
  | .nfXASqRightPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXASqRightPred z → z = nfXA
  | .nfUSqLiftRightSPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUSqLiftRightSPred z → z = nfU
  | .nfXADecorRightPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXADecorRightPred z → z = nfXA
  | .nfUDecorLiftRightSPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorLiftRightSPred z → z = nfU
  | .nfXADecorLeftPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXADecorLeftPred z → z = nfXA
  | .nfUDecorLiftLeftSPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorLiftLeftSPred z → z = nfU
  | .nfUStablePred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUStablePred z → z = nfU
  | .nfUHolePred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUHolePred z → z = nfU
  | .nfUDecorHolePred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorHolePred z → z = nfU ∨ z = nfUHolePred
  | .nfXASqAPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXASqAPred z → z = nfXA ∨ z = nfXASqRightPred
  | .nfUSqLiftAPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUSqLiftAPred z → z = nfU ∨ z = nfUSqLiftRightSPred
  | .nfUDecorRightPred =>
      ∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorRightPred z → z = nfU ∨ z = nfM

theorem targetKernelEnvelope_of_target (tg : CoreKernelTarget) :
    TargetKernelEnvelope tg := by
  cases tg with
  | nfXASqRightPred =>
      intro z hz
      exact NFStepR_from_nfXASqRightPred_eq_nfXA (z := z) hz
  | nfUSqLiftRightSPred =>
      intro z hz
      exact NFStepR_from_nfUSqLiftRightSPred_eq_nfU (z := z) hz
  | nfXADecorRightPred =>
      intro z hz
      exact NFStepR_from_nfXADecorRightPred_eq_nfXA (z := z) hz
  | nfUDecorLiftRightSPred =>
      intro z hz
      exact NFStepR_from_nfUDecorLiftRightSPred_eq_nfU (z := z) hz
  | nfXADecorLeftPred =>
      intro z hz
      exact NFStepR_from_nfXADecorLeftPred_eq_nfXA (z := z) hz
  | nfUDecorLiftLeftSPred =>
      intro z hz
      exact NFStepR_from_nfUDecorLiftLeftSPred_eq_nfU (z := z) hz
  | nfUStablePred =>
      intro z hz
      exact NFStepR_from_nfUStablePred_eq_nfU (z := z) hz
  | nfUHolePred =>
      intro z hz
      exact NFStepR_from_nfUHolePred_eq_nfU (z := z) hz
  | nfUDecorHolePred =>
      intro z hz
      exact NFStepR_from_nfUDecorHolePred_cases (z := z) hz
  | nfXASqAPred =>
      intro z hz
      exact NFStepR_from_nfXASqAPred_cases (z := z) hz
  | nfUSqLiftAPred =>
      intro z hz
      exact NFStepR_from_nfUSqLiftAPred_cases (z := z) hz
  | nfUDecorRightPred =>
      intro z hz
      exact NFStepR_from_nfUDecorRightPred_cases (z := z) hz

/- =========================================================
   4. kernel -> canonical row realization
   ========================================================= -/

structure KernelRowRealized (tg : CoreKernelTarget) where
  row_eq :
    corePurifiedRowOfTarget tg =
      corePurifiedRowFromKernelData (coreKernelClass tg) (coreKernelShell tg)
  cert :
    PurifiedCtxRowCertificate ctxNFOfTag
      (coreNFOfTarget tg) (corePurifiedRowOfTarget tg)

def kernelRowRealized_of_target (tg : CoreKernelTarget) :
    KernelRowRealized tg := {
  row_eq := corePurifiedRowOfTarget_via_kernel_data tg
  cert := corePurifiedRow_certificate_of_target tg
}
/- =========================================================
   5. pure / bridge-split separation
   ========================================================= -/

theorem bridgeSplit_iff_target_eq_nfUDecorRightPred
    (tg : CoreKernelTarget) :
    coreKernelRegime (coreKernelClass tg) = .bridgeSplit
      ↔ tg = .nfUDecorRightPred := by
  cases tg <;> simp [coreKernelClass, coreKernelRegime]

theorem pure_iff_target_ne_nfUDecorRightPred
    (tg : CoreKernelTarget) :
    coreKernelRegime (coreKernelClass tg) = .pure
      ↔ tg ≠ .nfUDecorRightPred := by
  cases tg <;> simp [coreKernelClass, coreKernelRegime]

theorem pure_prototype_channel_purity :
    ChannelPure purifiedCtxProfile_nfXASqAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUDecorRightPred_decor.toCtxProfile := by
  exact core_row_channel_purity_theorem

theorem pure_prototype_branching_isolation :
    purifiedCtxProfile_nfXASqAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUDecorRightPred_decor.tags.length = 1 := by
  exact core_row_branching_isolation_theorem

theorem bridgeSplit_prototype_semantics :
    (purifiedCtxProfile_nfUDecorRightPred_decor.channel? = some .right ∧
     purifiedCtxProfile_nfUDecorRightPred_decor.tags = [.nfU]) ∧
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUDecorRightPred z → z = nfM) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorRightPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorRightPred z → z = nfU ∨ z = nfM) := by
  rcases bridgeKernel_rulewise_envelope_theorem with ⟨hsq, hdecor, hstep⟩
  exact ⟨uDecorRightPred_decor_right_only_singleton_theorem, hsq, hdecor, hstep⟩

/- =========================================================
   6. global organic spine
   ========================================================= -/

structure OrganicCoreSpine (tg : CoreKernelTarget) where
  audit : KernelAuditClosed tg
  envelope : TargetKernelEnvelope tg
  row : KernelRowRealized tg

def core_target_organic_spine (tg : CoreKernelTarget) :
    OrganicCoreSpine tg := {
  audit := kernelAuditClosed_of_target tg
  envelope := targetKernelEnvelope_of_target tg
  row := kernelRowRealized_of_target tg
}

structure GlobalOrganicSpine where
  rootAudit : RootAuditClosed
  coreSpine : ∀ tg : CoreKernelTarget, OrganicCoreSpine tg
  bridgeSplitChar :
    ∀ tg : CoreKernelTarget,
      coreKernelRegime (coreKernelClass tg) = .bridgeSplit
        ↔ tg = .nfUDecorRightPred
  pureChannelPurity :
    ChannelPure purifiedCtxProfile_nfXASqAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUDecorRightPred_decor.toCtxProfile
  pureBranchingIsolation :
    purifiedCtxProfile_nfXASqAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUDecorRightPred_decor.tags.length = 1
  bridgeSplitSemantics :
    (purifiedCtxProfile_nfUDecorRightPred_decor.channel? = some .right ∧
     purifiedCtxProfile_nfUDecorRightPred_decor.tags = [.nfU]) ∧
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUDecorRightPred z → z = nfM) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorRightPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorRightPred z → z = nfU ∨ z = nfM)

end OrganicSpine

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
