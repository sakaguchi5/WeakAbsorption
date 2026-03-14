import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_KernelTheorems
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Profiles

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

section CorePurifiedContextRows

private def emptyPurifiedCtxProfile : PurifiedCtxProfile :=
  { channel? := none, tags := [] }

private def rightSingleton_nfXA : PurifiedCtxProfile :=
  { channel? := some .right, tags := [.nfXA] }

private def leftSingleton_nfU : PurifiedCtxProfile :=
  { channel? := some .left, tags := [.nfU] }

private def rootSingleton_nfU : PurifiedCtxProfile :=
  { channel? := some .root, tags := [.nfU] }

private def rootSingleton_nfUHolePred : PurifiedCtxProfile :=
  { channel? := some .root, tags := [.nfUHolePred] }

private def leftSingleton_nfM : PurifiedCtxProfile :=
  { channel? := some .left, tags := [.nfM] }

/--
Canonical target-indexed purified-row table. This is now the single source of truth;
legacy `corePurifiedRow_nf...` names below are reducible compatibility abbreviations.
-/
def canonicalCorePurifiedRow : CoreKernelTarget -> PurifiedCtxRow
  | .nfXASqRightPred =>
      { sqAbsorb := rightSingleton_nfXA
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile }
  | .nfUSqLiftRightSPred =>
      { sqAbsorb := leftSingleton_nfU
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile }
  | .nfXADecorRightPred =>
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := rightSingleton_nfXA
        c2c1 := emptyPurifiedCtxProfile }
  | .nfUDecorLiftRightSPred =>
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := leftSingleton_nfU
        c2c1 := emptyPurifiedCtxProfile }
  | .nfXADecorLeftPred =>
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := rightSingleton_nfXA
        c2c1 := emptyPurifiedCtxProfile }
  | .nfUDecorLiftLeftSPred =>
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := leftSingleton_nfU
        c2c1 := emptyPurifiedCtxProfile }
  | .nfUStablePred =>
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := leftSingleton_nfU
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile }
  | .nfUHolePred =>
      { sqAbsorb := rootSingleton_nfU
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := rootSingleton_nfU }
  | .nfUDecorHolePred =>
      { sqAbsorb := rootSingleton_nfUHolePred
        sqStable := emptyPurifiedCtxProfile
        decor := rootSingleton_nfU
        c2c1 := emptyPurifiedCtxProfile }
  | .nfXASqAPred =>
      { sqAbsorb := purifiedCtxProfile_nfXASqAPred_sqAbsorb
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile }
  | .nfUSqLiftAPred =>
      { sqAbsorb := purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile }
  | .nfUDecorRightPred =>
      { sqAbsorb := leftSingleton_nfM
        sqStable := emptyPurifiedCtxProfile
        decor := purifiedCtxProfile_nfUDecorRightPred_decor
        c2c1 := emptyPurifiedCtxProfile }

abbrev corePurifiedRow_nfXASqRightPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfXASqRightPred

abbrev corePurifiedRow_nfUSqLiftRightSPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUSqLiftRightSPred

abbrev corePurifiedRow_nfXADecorRightPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfXADecorRightPred

abbrev corePurifiedRow_nfUDecorLiftRightSPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUDecorLiftRightSPred

abbrev corePurifiedRow_nfXADecorLeftPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfXADecorLeftPred

abbrev corePurifiedRow_nfUDecorLiftLeftSPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUDecorLiftLeftSPred

abbrev corePurifiedRow_nfUStablePred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUStablePred

abbrev corePurifiedRow_nfUHolePred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUHolePred

abbrev corePurifiedRow_nfUDecorHolePred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUDecorHolePred

abbrev corePurifiedRow_nfXASqAPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfXASqAPred

abbrev corePurifiedRow_nfUSqLiftAPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUSqLiftAPred

abbrev corePurifiedRow_nfUDecorRightPred : PurifiedCtxRow :=
  canonicalCorePurifiedRow .nfUDecorRightPred

theorem corePurifiedRows_uniform_shapes :
    corePurifiedRow_nfXASqRightPred.sqAbsorb = rightSingleton_nfXA ∧
    corePurifiedRow_nfXASqRightPred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXASqRightPred.decor = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXASqRightPred.c2c1 = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUSqLiftRightSPred.sqAbsorb = leftSingleton_nfU ∧
    corePurifiedRow_nfUSqLiftRightSPred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUSqLiftRightSPred.decor = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUSqLiftRightSPred.c2c1 = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXADecorRightPred.sqAbsorb = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXADecorRightPred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXADecorRightPred.decor = rightSingleton_nfXA ∧
    corePurifiedRow_nfXADecorRightPred.c2c1 = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorLiftRightSPred.sqAbsorb = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorLiftRightSPred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorLiftRightSPred.decor = leftSingleton_nfU ∧
    corePurifiedRow_nfUDecorLiftRightSPred.c2c1 = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXADecorLeftPred.sqAbsorb = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXADecorLeftPred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfXADecorLeftPred.decor = rightSingleton_nfXA ∧
    corePurifiedRow_nfXADecorLeftPred.c2c1 = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorLiftLeftSPred.sqAbsorb = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorLiftLeftSPred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorLiftLeftSPred.decor = leftSingleton_nfU ∧
    corePurifiedRow_nfUDecorLiftLeftSPred.c2c1 = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUStablePred.sqAbsorb = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUStablePred.sqStable = leftSingleton_nfU ∧
    corePurifiedRow_nfUStablePred.decor = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUStablePred.c2c1 = emptyPurifiedCtxProfile := by
  simp [canonicalCorePurifiedRow, corePurifiedRow_nfXASqRightPred, corePurifiedRow_nfUSqLiftRightSPred,
    corePurifiedRow_nfXADecorRightPred, corePurifiedRow_nfUDecorLiftRightSPred,
    corePurifiedRow_nfXADecorLeftPred, corePurifiedRow_nfUDecorLiftLeftSPred,
    corePurifiedRow_nfUStablePred, rightSingleton_nfXA, leftSingleton_nfU,
    emptyPurifiedCtxProfile]

theorem corePurifiedRows_sa_rows_are_repaired :
    corePurifiedRow_nfXASqRightPred =
      { sqAbsorb := rightSingleton_nfXA
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile } ∧
    corePurifiedRow_nfUSqLiftRightSPred =
      { sqAbsorb := leftSingleton_nfU
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile } := by
  simp [canonicalCorePurifiedRow, corePurifiedRow_nfXASqRightPred, corePurifiedRow_nfUSqLiftRightSPred,
    rightSingleton_nfXA, leftSingleton_nfU, emptyPurifiedCtxProfile]

theorem corePurifiedRows_decor_rows_are_honest :
    corePurifiedRow_nfXADecorRightPred =
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := rightSingleton_nfXA
        c2c1 := emptyPurifiedCtxProfile } ∧
    corePurifiedRow_nfUDecorLiftRightSPred =
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := leftSingleton_nfU
        c2c1 := emptyPurifiedCtxProfile } ∧
    corePurifiedRow_nfXADecorLeftPred =
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := rightSingleton_nfXA
        c2c1 := emptyPurifiedCtxProfile } ∧
    corePurifiedRow_nfUDecorLiftLeftSPred =
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := leftSingleton_nfU
        c2c1 := emptyPurifiedCtxProfile } := by
  simp [canonicalCorePurifiedRow, corePurifiedRow_nfXADecorRightPred, corePurifiedRow_nfUDecorLiftRightSPred,
    corePurifiedRow_nfXADecorLeftPred, corePurifiedRow_nfUDecorLiftLeftSPred,
    emptyPurifiedCtxProfile, rightSingleton_nfXA, leftSingleton_nfU]

theorem corePurifiedRows_hole_shapes :
    corePurifiedRow_nfUHolePred.sqAbsorb = rootSingleton_nfU ∧
    corePurifiedRow_nfUHolePred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUHolePred.decor = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUHolePred.c2c1 = rootSingleton_nfU ∧
    corePurifiedRow_nfUDecorHolePred.sqAbsorb = rootSingleton_nfUHolePred ∧
    corePurifiedRow_nfUDecorHolePred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorHolePred.decor = rootSingleton_nfU ∧
    corePurifiedRow_nfUDecorHolePred.c2c1 = emptyPurifiedCtxProfile := by
  simp [canonicalCorePurifiedRow, corePurifiedRow_nfUHolePred, corePurifiedRow_nfUDecorHolePred,
    rootSingleton_nfU, rootSingleton_nfUHolePred, emptyPurifiedCtxProfile]

theorem corePurifiedRows_stable_shape :
    corePurifiedRow_nfUStablePred =
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := leftSingleton_nfU
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile } := by
  simp [canonicalCorePurifiedRow, corePurifiedRow_nfUStablePred, emptyPurifiedCtxProfile, leftSingleton_nfU]

/--
After the stable/bridge re-audit, the bridge-split shapes that are asserted as exact are the
AA branching cells together with the exact bridge support row.
-/
theorem corePurifiedRows_bridgeSplit_shapes :
    corePurifiedRow_nfXASqAPred.sqAbsorb = purifiedCtxProfile_nfXASqAPred_sqAbsorb ∧
    corePurifiedRow_nfUSqLiftAPred.sqAbsorb = purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb ∧
    corePurifiedRow_nfUDecorRightPred.sqAbsorb = leftSingleton_nfM ∧
    corePurifiedRow_nfUDecorRightPred.sqStable = emptyPurifiedCtxProfile ∧
    corePurifiedRow_nfUDecorRightPred.decor = purifiedCtxProfile_nfUDecorRightPred_decor ∧
    corePurifiedRow_nfUDecorRightPred.c2c1 = emptyPurifiedCtxProfile := by
  simp [canonicalCorePurifiedRow, corePurifiedRow_nfXASqAPred, corePurifiedRow_nfUSqLiftAPred,
    corePurifiedRow_nfUDecorRightPred, leftSingleton_nfM, emptyPurifiedCtxProfile]



def corePurifiedRowFromKernelData
    (cls : CoreKernelClass) (shell : CoreKernelShell) : PurifiedCtxRow :=
  match cls, shell with
  | .saKernel, .rightShell => canonicalCorePurifiedRow .nfXASqRightPred
  | .saKernel, .leftLift => canonicalCorePurifiedRow .nfUSqLiftRightSPred
  | .decorRightKernel, .rightShell => canonicalCorePurifiedRow .nfXADecorRightPred
  | .decorRightKernel, .leftLift => canonicalCorePurifiedRow .nfUDecorLiftRightSPred
  | .decorLeftKernel, .rightShell => canonicalCorePurifiedRow .nfXADecorLeftPred
  | .decorLeftKernel, .leftLift => canonicalCorePurifiedRow .nfUDecorLiftLeftSPred
  | .aaKernel, .rightShell => canonicalCorePurifiedRow .nfXASqAPred
  | .aaKernel, .leftLift => canonicalCorePurifiedRow .nfUSqLiftAPred
  | .stableKernel, .leftLift => canonicalCorePurifiedRow .nfUStablePred
  | .holeKernel, .rootShell => canonicalCorePurifiedRow .nfUHolePred
  | .decorHoleKernel, .rootShell => canonicalCorePurifiedRow .nfUDecorHolePred
  | .bridgeKernel, .bridgeSplitShell => canonicalCorePurifiedRow .nfUDecorRightPred
  | _, _ =>
      { sqAbsorb := emptyPurifiedCtxProfile
        sqStable := emptyPurifiedCtxProfile
        decor := emptyPurifiedCtxProfile
        c2c1 := emptyPurifiedCtxProfile }

def corePurifiedRowOfTarget (tg : CoreKernelTarget) : PurifiedCtxRow :=
  canonicalCorePurifiedRow tg

theorem corePurifiedRowOfTarget_eq_legacy
    (tg : CoreKernelTarget) :
    corePurifiedRowOfTarget tg =
      match tg with
      | .nfXASqRightPred => corePurifiedRow_nfXASqRightPred
      | .nfUSqLiftRightSPred => corePurifiedRow_nfUSqLiftRightSPred
      | .nfXADecorRightPred => corePurifiedRow_nfXADecorRightPred
      | .nfUDecorLiftRightSPred => corePurifiedRow_nfUDecorLiftRightSPred
      | .nfXADecorLeftPred => corePurifiedRow_nfXADecorLeftPred
      | .nfUDecorLiftLeftSPred => corePurifiedRow_nfUDecorLiftLeftSPred
      | .nfUStablePred => corePurifiedRow_nfUStablePred
      | .nfUHolePred => corePurifiedRow_nfUHolePred
      | .nfUDecorHolePred => corePurifiedRow_nfUDecorHolePred
      | .nfXASqAPred => corePurifiedRow_nfXASqAPred
      | .nfUSqLiftAPred => corePurifiedRow_nfUSqLiftAPred
      | .nfUDecorRightPred => corePurifiedRow_nfUDecorRightPred := by
  cases tg <;> rfl

theorem corePurifiedRowOfTarget_via_kernel_data
    (tg : CoreKernelTarget) :
    corePurifiedRowOfTarget tg =
      corePurifiedRowFromKernelData (coreKernelClass tg) (coreKernelShell tg) := by
  cases tg <;> rfl

theorem canonicalCorePurifiedRow_eliminates_legacy_duplication :
    corePurifiedRowOfTarget .nfXASqRightPred = canonicalCorePurifiedRow .nfXASqRightPred ∧
    corePurifiedRowOfTarget .nfUSqLiftRightSPred = canonicalCorePurifiedRow .nfUSqLiftRightSPred ∧
    corePurifiedRowOfTarget .nfXADecorRightPred = canonicalCorePurifiedRow .nfXADecorRightPred ∧
    corePurifiedRowOfTarget .nfUDecorLiftRightSPred = canonicalCorePurifiedRow .nfUDecorLiftRightSPred ∧
    corePurifiedRowOfTarget .nfXADecorLeftPred = canonicalCorePurifiedRow .nfXADecorLeftPred ∧
    corePurifiedRowOfTarget .nfUDecorLiftLeftSPred = canonicalCorePurifiedRow .nfUDecorLiftLeftSPred ∧
    corePurifiedRowOfTarget .nfUStablePred = canonicalCorePurifiedRow .nfUStablePred ∧
    corePurifiedRowOfTarget .nfUHolePred = canonicalCorePurifiedRow .nfUHolePred ∧
    corePurifiedRowOfTarget .nfUDecorHolePred = canonicalCorePurifiedRow .nfUDecorHolePred ∧
    corePurifiedRowOfTarget .nfXASqAPred = canonicalCorePurifiedRow .nfXASqAPred ∧
    corePurifiedRowOfTarget .nfUSqLiftAPred = canonicalCorePurifiedRow .nfUSqLiftAPred ∧
    corePurifiedRowOfTarget .nfUDecorRightPred = canonicalCorePurifiedRow .nfUDecorRightPred := by
  repeat' constructor <;> simp [corePurifiedRowOfTarget]

theorem corePurifiedRows_are_kernel_derived :
    corePurifiedRowOfTarget .nfXASqRightPred = corePurifiedRow_nfXASqRightPred ∧
    corePurifiedRowOfTarget .nfUSqLiftRightSPred = corePurifiedRow_nfUSqLiftRightSPred ∧
    corePurifiedRowOfTarget .nfXADecorRightPred = corePurifiedRow_nfXADecorRightPred ∧
    corePurifiedRowOfTarget .nfUDecorLiftRightSPred = corePurifiedRow_nfUDecorLiftRightSPred ∧
    corePurifiedRowOfTarget .nfXADecorLeftPred = corePurifiedRow_nfXADecorLeftPred ∧
    corePurifiedRowOfTarget .nfUDecorLiftLeftSPred = corePurifiedRow_nfUDecorLiftLeftSPred ∧
    corePurifiedRowOfTarget .nfUStablePred = corePurifiedRow_nfUStablePred ∧
    corePurifiedRowOfTarget .nfUHolePred = corePurifiedRow_nfUHolePred ∧
    corePurifiedRowOfTarget .nfUDecorHolePred = corePurifiedRow_nfUDecorHolePred ∧
    corePurifiedRowOfTarget .nfXASqAPred = corePurifiedRow_nfXASqAPred ∧
    corePurifiedRowOfTarget .nfUSqLiftAPred = corePurifiedRow_nfUSqLiftAPred ∧
    corePurifiedRowOfTarget .nfUDecorRightPred = corePurifiedRow_nfUDecorRightPred := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfXASqRightPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUSqLiftRightSPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfXADecorRightPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUDecorLiftRightSPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfXADecorLeftPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUDecorLiftLeftSPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUStablePred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUHolePred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUDecorHolePred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfXASqAPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUSqLiftAPred)
  · simpa using (corePurifiedRowOfTarget_eq_legacy .nfUDecorRightPred)

theorem corePurifiedRows_global_completion :
    ∀ tg : CoreKernelTarget,
      (corePurifiedRowOfTarget tg =
        match tg with
        | .nfXASqRightPred => corePurifiedRow_nfXASqRightPred
        | .nfUSqLiftRightSPred => corePurifiedRow_nfUSqLiftRightSPred
        | .nfXADecorRightPred => corePurifiedRow_nfXADecorRightPred
        | .nfUDecorLiftRightSPred => corePurifiedRow_nfUDecorLiftRightSPred
        | .nfXADecorLeftPred => corePurifiedRow_nfXADecorLeftPred
        | .nfUDecorLiftLeftSPred => corePurifiedRow_nfUDecorLiftLeftSPred
        | .nfUStablePred => corePurifiedRow_nfUStablePred
        | .nfUHolePred => corePurifiedRow_nfUHolePred
        | .nfUDecorHolePred => corePurifiedRow_nfUDecorHolePred
        | .nfXASqAPred => corePurifiedRow_nfXASqAPred
        | .nfUSqLiftAPred => corePurifiedRow_nfUSqLiftAPred
        | .nfUDecorRightPred => corePurifiedRow_nfUDecorRightPred) ∧
      coreKernelCodomainStatus (coreKernelClass tg) = .settled ∧
      coreKernelSupportStatus (coreKernelClass tg) = .exact ∧
      coreKernelRegime (coreKernelClass tg) =
        match tg with
        | .nfUDecorRightPred => .bridgeSplit
        | _ => .pure := by
  intro tg
  cases tg <;> simp [corePurifiedRowOfTarget, canonicalCorePurifiedRow,
    coreKernelClass, coreKernelCodomainStatus,
    coreKernelSupportStatus, coreKernelRegime]

theorem corePurifiedRows_proto_channel_pure :
    ChannelPure corePurifiedRow_nfXASqRightPred.sqAbsorb.toCtxProfile ∧
    ChannelPure corePurifiedRow_nfUSqLiftRightSPred.sqAbsorb.toCtxProfile ∧
    ChannelPure corePurifiedRow_nfXADecorRightPred.decor.toCtxProfile ∧
    ChannelPure corePurifiedRow_nfUDecorLiftRightSPred.decor.toCtxProfile ∧
    ChannelPure corePurifiedRow_nfXADecorLeftPred.decor.toCtxProfile ∧
    ChannelPure corePurifiedRow_nfUDecorLiftLeftSPred.decor.toCtxProfile ∧
    ChannelPure corePurifiedRow_nfUStablePred.sqStable.toCtxProfile ∧
    ChannelPure corePurifiedRow_nfUHolePred.sqAbsorb.toCtxProfile := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfXASqRightPred, rightSingleton_nfXA] using
      (purifiedProfile_channelPure rightSingleton_nfXA )
  · simpa [corePurifiedRow_nfUSqLiftRightSPred, leftSingleton_nfU] using
      (purifiedProfile_channelPure leftSingleton_nfU )
  · simpa [corePurifiedRow_nfXADecorRightPred, rightSingleton_nfXA] using
      (purifiedProfile_channelPure rightSingleton_nfXA )
  · simpa [corePurifiedRow_nfUDecorLiftRightSPred, leftSingleton_nfU] using
      (purifiedProfile_channelPure leftSingleton_nfU )
  · simpa [corePurifiedRow_nfXADecorLeftPred, rightSingleton_nfXA] using
      (purifiedProfile_channelPure rightSingleton_nfXA )
  · simpa [corePurifiedRow_nfUDecorLiftLeftSPred, leftSingleton_nfU] using
      (purifiedProfile_channelPure leftSingleton_nfU )
  · simpa [corePurifiedRow_nfUStablePred, leftSingleton_nfU] using
      (purifiedProfile_channelPure leftSingleton_nfU )
  · simpa [corePurifiedRow_nfUHolePred, rootSingleton_nfU] using
      (purifiedProfile_channelPure rootSingleton_nfU )



structure PurifiedCtxRowCertificate {α : Type}
    (interp : CtxNFTag -> NormalForm α)
    (src : NormalForm α)
    (row : PurifiedCtxRow) : Prop where
  sqAbsorb :
    PurifiedCtxCellProfileCertificate interp
      (fun s z => NFSqStepCtx (α := α) s z) src row.sqAbsorb
  sqStable :
    PurifiedCtxCellProfileCertificate interp
      (fun s z => NFSqStableStepCtx (α := α) s z) src row.sqStable
  decor :
    PurifiedCtxCellProfileCertificate interp
      (fun s z => NFDecorStepCtx (α := α) s z) src row.decor
  c2c1 :
    PurifiedCtxCellProfileCertificate interp
      (fun s z => NFC2C1StepCtx (α := α) s z) src row.c2c1

private theorem nfXASqRightPred_sqAbsorb_to_nfXA :
    NFSqStepCtx (α := V) nfXASqRightPred nfXA := by
  refine ⟨Ctx.right x (Ctx.right s Ctx.hole), x, x, ?_, ?_⟩
  ·
    change xASqRightSPredTerm
      = Ctx.plug (Ctx.right x (Ctx.right s Ctx.hole))
          (((x.op x).op (x.op x)))
    simp [Ctx.plug, xASqRightSPredTerm, A, s, x]
  ·
    change xATerm
      = Ctx.plug (Ctx.right x (Ctx.right s Ctx.hole))
          (x.op x)
    simp [Ctx.plug, xATerm, A, s, x]

private theorem nfUSqLiftRightSPred_sqAbsorb_to_nfU :
    NFSqStepCtx (α := V) nfUSqLiftRightSPred nfU := by
  refine ⟨Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s, x, x, ?_, ?_⟩
  ·
    change uSqLiftRightSPredTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s)
          (((x.op x).op (x.op x)))
    simp [Ctx.plug, uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x]
  ·
    change uTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s)
          (x.op x)
    simp [Ctx.plug, uTerm, A, s, x]

private theorem nfXADecorRightPred_decor_to_nfXA :
    NFDecorStepCtx (α := V) nfXADecorRightPred nfXA := by
  refine ⟨Ctx.right x (Ctx.right s Ctx.hole), x, x, ?_, ?_⟩
  ·
    change xADecorRightSPredTerm
      = Ctx.plug (Ctx.right x (Ctx.right s Ctx.hole))
          ((x.op x).op (x.op (x.op x)))
    simp [Ctx.plug, xADecorRightSPredTerm, s, x]
  ·
    change xATerm = Ctx.plug (Ctx.right x (Ctx.right s Ctx.hole)) (x.op x)
    simp [Ctx.plug, xATerm, A, s, x]

private theorem nfUDecorLiftRightSPred_decor_to_nfU :
    NFDecorStepCtx (α := V) nfUDecorLiftRightSPred nfU := by
  refine ⟨Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s, x, x, ?_, ?_⟩
  ·
    change uDecorLiftRightSPredTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s)
          ((x.op x).op (x.op (x.op x)))
    simp [Ctx.plug, uDecorLiftRightSPredTerm, xADecorRightSPredTerm, s, x]
  ·
    change uTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s)
          (x.op x)
    simp [Ctx.plug, uTerm, A, s, x]

private theorem nfXADecorLeftPred_decor_to_nfXA :
    NFDecorStepCtx (α := V) nfXADecorLeftPred nfXA := by
  refine ⟨Ctx.right x (Ctx.left Ctx.hole s), x, x, ?_, ?_⟩
  ·
    change xADecorLeftSPredTerm
      = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole s))
          (((x.op x).op (x.op (x.op x))))
    simp [Ctx.plug, xADecorLeftSPredTerm, s, x]
  ·
    change xATerm = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole s)) (x.op x)
    simp [Ctx.plug, xATerm, A, s, x]

private theorem nfUDecorLiftLeftSPred_decor_to_nfU :
    NFDecorStepCtx (α := V) nfUDecorLiftLeftSPred nfU := by
  refine ⟨Ctx.left (Ctx.right x (Ctx.left Ctx.hole s)) s, x, x, ?_, ?_⟩
  ·
    change uDecorLiftLeftSPredTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole s)) s)
          (((x.op x).op (x.op (x.op x))))
    simp [Ctx.plug, uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, s, x]
  ·
    change uTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole s)) s)
          (x.op x)
    simp [Ctx.plug, uTerm, A, s, x]

private theorem nfUStablePred_sqStable_to_nfU :
    NFSqStableStepCtx (α := V) nfUStablePred nfU := by
  refine ⟨Ctx.left (Ctx.right x Ctx.hole) s, x, x, ?_, ?_⟩
  ·
    change uStablePredTerm
      = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s)
          ((((x.op x).op (x.op x)).op x))
    simp [Ctx.plug, uStablePredTerm, xAStablePredTerm, A, s, x]
  ·
    change uTerm
      = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s)
          ((x.op x).op (x.op x))
    simp [Ctx.plug, uTerm, A, s, x]

private theorem nfUHolePred_sqAbsorb_to_nfU :
    NFSqStepCtx (α := V) nfUHolePred nfU := by
  refine ⟨Ctx.hole, xATerm, s, ?_, ?_⟩
  ·
    change uHolePredTerm = Ctx.plug Ctx.hole (((xATerm.op s).op (s.op s)))
    simp [Ctx.plug, uHolePredTerm, uTerm, xATerm, A, s, x]
  ·
    change uTerm = Ctx.plug Ctx.hole (xATerm.op s)
    simp [Ctx.plug, uTerm, xATerm, A, s, x]

private theorem nfUHolePred_c2c1_to_nfU :
    NFC2C1StepCtx (α := V) nfUHolePred nfU := by
  refine ⟨Ctx.hole, x, s, s, ?_, ?_⟩
  ·
    change uHolePredTerm
      = Ctx.plug Ctx.hole ((((x.op (s.op s)).op s).op (s.op s)))
    simp [Ctx.plug, uHolePredTerm, uTerm, A, s, x]
  ·
    change uTerm = Ctx.plug Ctx.hole ((x.op (s.op s)).op s)
    simp [Ctx.plug, uTerm,  A, s, x]

private theorem nfUDecorHolePred_sqAbsorb_to_nfUHolePred :
    NFSqStepCtx (α := V) nfUDecorHolePred nfUHolePred := by
  refine ⟨Ctx.right uTerm (Ctx.right s Ctx.hole), x, x, ?_, ?_⟩
  ·
    change uDecorHolePredTerm
      = Ctx.plug (Ctx.right uTerm (Ctx.right s Ctx.hole))
          (((x.op x).op (x.op x)))
    simp [Ctx.plug, uDecorHolePredTerm, uTerm, A, s, x]
  ·
    change uHolePredTerm
      = Ctx.plug (Ctx.right uTerm (Ctx.right s Ctx.hole))
          (x.op x)
    simp [Ctx.plug, uHolePredTerm, uTerm, A, s, x]

private theorem nfUDecorHolePred_decor_to_nfU :
    NFDecorStepCtx (α := V) nfUDecorHolePred nfU := by
  refine ⟨Ctx.hole, xATerm, s, ?_, ?_⟩
  ·
    change uDecorHolePredTerm
      = Ctx.plug Ctx.hole ((xATerm.op s).op (s.op (s.op s)))
    simp [Ctx.plug, uDecorHolePredTerm, uTerm, xATerm, A, s, x]
  ·
    change uTerm = Ctx.plug Ctx.hole (xATerm.op s)
    simp [Ctx.plug, uTerm, xATerm, A, s, x]

private theorem nfUDecorRightPred_sqAbsorb_to_nfM :
    NFSqStepCtx (α := V) nfUDecorRightPred nfM := by
  refine ⟨Ctx.left (Ctx.right x Ctx.hole) (s.op vTerm), x, x, ?_, ?_⟩
  ·
    change uDecorRightPredTerm
      = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) (s.op vTerm))
          (((x.op x).op (x.op x)))
    simp [Ctx.plug, uDecorRightPredTerm, xATerm, vTerm, A, s, x]
  ·
    change mTerm
      = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) (s.op vTerm))
          (x.op x)
    simp [Ctx.plug, mTerm, vTerm, s, x]

private theorem rowCert_nfXASqRightPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfXASqRightPred corePurifiedRow_nfXASqRightPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfXASqRightPred, rightSingleton_nfXA] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfXASqRightPred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        .right .nfXA
        nfXASqRightPred_sqAbsorb_to_nfXA
        (by intro z hz; exact sqAbsorb_succ_from_nfXASqRightPred_eq_nfXA (z := z) hz))
  · simpa [corePurifiedRow_nfXASqRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXASqRightPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfXASqRightPred (z := z) hz))
  · simpa [corePurifiedRow_nfXASqRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXASqRightPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        (by intro z hz; exact no_decor_succ_from_nfXASqRightPred (z := z) hz))
  · simpa [corePurifiedRow_nfXASqRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXASqRightPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfXASqRightPred (z := z) hz))

private theorem rowCert_nfUSqLiftRightSPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUSqLiftRightSPred corePurifiedRow_nfUSqLiftRightSPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUSqLiftRightSPred, leftSingleton_nfU] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUSqLiftRightSPred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        .left .nfU
        nfUSqLiftRightSPred_sqAbsorb_to_nfU
        (by intro z hz; exact sqAbsorb_succ_from_nfUSqLiftRightSPred_eq_nfU (z := z) hz))
  · simpa [corePurifiedRow_nfUSqLiftRightSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUSqLiftRightSPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfUSqLiftRightSPred (z := z) hz))
  · simpa [corePurifiedRow_nfUSqLiftRightSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUSqLiftRightSPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        (by intro z hz; exact no_decor_succ_from_nfUSqLiftRightSPred (z := z) hz))
  · simpa [corePurifiedRow_nfUSqLiftRightSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUSqLiftRightSPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfUSqLiftRightSPred (z := z) hz))

private theorem rowCert_nfXADecorRightPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfXADecorRightPred corePurifiedRow_nfXADecorRightPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfXADecorRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXADecorRightPred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        (by intro z hz; exact no_sqAbsorb_succ_from_nfXADecorRightPred (z := z) hz))
  · simpa [corePurifiedRow_nfXADecorRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXADecorRightPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfXADecorRightPred (z := z) hz))
  · simpa [corePurifiedRow_nfXADecorRightPred, rightSingleton_nfXA] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfXADecorRightPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        .right .nfXA
        nfXADecorRightPred_decor_to_nfXA
        (by intro z hz; exact decor_step_from_nfXADecorRightPred_eq_nfXA (z := z) hz))
  · simpa [corePurifiedRow_nfXADecorRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXADecorRightPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfXADecorRightPred (z := z) hz))

private theorem rowCert_nfUDecorLiftRightSPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUDecorLiftRightSPred corePurifiedRow_nfUDecorLiftRightSPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUDecorLiftRightSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorLiftRightSPred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        (by intro z hz; exact no_sqAbsorb_succ_from_nfUDecorLiftRightSPred (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorLiftRightSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorLiftRightSPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfUDecorLiftRightSPred (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorLiftRightSPred, leftSingleton_nfU] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUDecorLiftRightSPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        .left .nfU
        nfUDecorLiftRightSPred_decor_to_nfU
        (by intro z hz; exact decor_step_from_nfUDecorLiftRightSPred_eq_nfU (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorLiftRightSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorLiftRightSPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfUDecorLiftRightSPred (z := z) hz))

private theorem rowCert_nfXADecorLeftPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfXADecorLeftPred corePurifiedRow_nfXADecorLeftPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfXADecorLeftPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXADecorLeftPred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        (by intro z hz; exact no_sqAbsorb_succ_from_nfXADecorLeftPred (z := z) hz))
  · simpa [corePurifiedRow_nfXADecorLeftPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXADecorLeftPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfXADecorLeftPred (z := z) hz))
  · simpa [corePurifiedRow_nfXADecorLeftPred, rightSingleton_nfXA] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfXADecorLeftPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        .right .nfXA
        nfXADecorLeftPred_decor_to_nfXA
        (by intro z hz; exact decor_step_from_nfXADecorLeftPred_eq_nfXA (z := z) hz))
  · simpa [corePurifiedRow_nfXADecorLeftPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXADecorLeftPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfXADecorLeftPred (z := z) hz))

private theorem rowCert_nfUDecorLiftLeftSPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUDecorLiftLeftSPred corePurifiedRow_nfUDecorLiftLeftSPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUDecorLiftLeftSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorLiftLeftSPred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        (by intro z hz; exact no_sqAbsorb_succ_from_nfUDecorLiftLeftSPred (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorLiftLeftSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorLiftLeftSPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfUDecorLiftLeftSPred (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorLiftLeftSPred, leftSingleton_nfU] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUDecorLiftLeftSPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        .left .nfU
        nfUDecorLiftLeftSPred_decor_to_nfU
        (by intro z hz; exact decor_step_from_nfUDecorLiftLeftSPred_eq_nfU (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorLiftLeftSPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorLiftLeftSPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfUDecorLiftLeftSPred (z := z) hz))

private theorem rowCert_nfUStablePred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUStablePred corePurifiedRow_nfUStablePred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUStablePred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUStablePred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        (by intro z hz; exact no_sqAbsorb_succ_from_nfUStablePred (z := z) hz))
  · simpa [corePurifiedRow_nfUStablePred, leftSingleton_nfU] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUStablePred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        .left .nfU
        nfUStablePred_sqStable_to_nfU
        (by intro z hz; exact sqStable_step_from_nfUStablePred_eq_nfU (z := z) hz))
  · simpa [corePurifiedRow_nfUStablePred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUStablePred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        (by intro z hz; exact no_decor_succ_from_nfUStablePred (z := z) hz))
  · simpa [corePurifiedRow_nfUStablePred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUStablePred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfUStablePred (z := z) hz))

private theorem rowCert_nfUHolePred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUHolePred corePurifiedRow_nfUHolePred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUHolePred, rootSingleton_nfU] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUHolePred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        .root .nfU
        nfUHolePred_sqAbsorb_to_nfU
        (by intro z hz; exact sqAbsorb_succ_from_nfUHolePred_eq_nfU (z := z) hz))
  · simpa [corePurifiedRow_nfUHolePred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUHolePred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfUHolePred (z := z) hz))
  · simpa [corePurifiedRow_nfUHolePred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUHolePred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        (by intro z hz; exact no_decor_succ_from_nfUHolePred (z := z) hz))
  · simpa [corePurifiedRow_nfUHolePred, rootSingleton_nfU] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUHolePred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        .root .nfU
        nfUHolePred_c2c1_to_nfU
        (by intro z hz; exact c2c1_succ_from_nfUHolePred_eq_nfU (z := z) hz))

private theorem rowCert_nfUDecorHolePred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUDecorHolePred corePurifiedRow_nfUDecorHolePred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUDecorHolePred, rootSingleton_nfUHolePred] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUDecorHolePred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        .root .nfUHolePred
        nfUDecorHolePred_sqAbsorb_to_nfUHolePred
        (by intro z hz; exact sqAbsorb_succ_from_nfUDecorHolePred_eq_nfUHolePred (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorHolePred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorHolePred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfUDecorHolePred (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorHolePred, rootSingleton_nfU] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUDecorHolePred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        .root .nfU
        nfUDecorHolePred_decor_to_nfU
        (by intro z hz; exact decor_succ_from_nfUDecorHolePred_eq_nfU (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorHolePred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorHolePred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfUDecorHolePred (z := z) hz))

private theorem rowCert_nfXASqAPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfXASqAPred corePurifiedRow_nfXASqAPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfXASqAPred] using
      purifiedCtxProfileCert_nfXASqAPred_sqAbsorb
  · simpa [corePurifiedRow_nfXASqAPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXASqAPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfXASqAPred (z := z) hz))
  · simpa [corePurifiedRow_nfXASqAPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXASqAPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        (by intro z hz; exact no_decor_succ_from_nfXASqAPred (z := z) hz))
  · simpa [corePurifiedRow_nfXASqAPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfXASqAPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfXASqAPred (z := z) hz))

private theorem rowCert_nfUSqLiftAPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUSqLiftAPred corePurifiedRow_nfUSqLiftAPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUSqLiftAPred] using
      purifiedCtxProfileCert_nfUSqLiftAPred_sqAbsorb
  · simpa [corePurifiedRow_nfUSqLiftAPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUSqLiftAPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfUSqLiftAPred (z := z) hz))
  · simpa [corePurifiedRow_nfUSqLiftAPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUSqLiftAPred)
        (Step := fun s z => NFDecorStepCtx (α := V) s z)
        (by intro z hz; exact no_decor_succ_from_nfUSqLiftAPred (z := z) hz))
  · simpa [corePurifiedRow_nfUSqLiftAPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUSqLiftAPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfUSqLiftAPred (z := z) hz))

private theorem rowCert_nfUDecorRightPred :
    PurifiedCtxRowCertificate ctxNFOfTag
      nfUDecorRightPred corePurifiedRow_nfUDecorRightPred := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [corePurifiedRow_nfUDecorRightPred, leftSingleton_nfM] using
      (purifiedCtxCellProfileCertificate_singleton
        (interp := ctxNFOfTag) (src := nfUDecorRightPred)
        (Step := fun s z => NFSqStepCtx (α := V) s z)
        .left .nfM
        nfUDecorRightPred_sqAbsorb_to_nfM
        (by intro z hz; exact sqAbsorb_succ_from_nfUDecorRightPred_eq_nfM (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorRightPred)
        (Step := fun s z => NFSqStableStepCtx (α := V) s z)
        (by intro z hz; exact no_sqStable_succ_from_nfUDecorRightPred (z := z) hz))
  · simpa [corePurifiedRow_nfUDecorRightPred] using
      purifiedCtxProfileCert_nfUDecorRightPred_decor
  · simpa [corePurifiedRow_nfUDecorRightPred, emptyPurifiedCtxProfile] using
      (purifiedCtxCellProfileCertificate_empty
        (interp := ctxNFOfTag) (src := nfUDecorRightPred)
        (Step := fun s z => NFC2C1StepCtx (α := V) s z)
        (by intro z hz; exact no_c2c1_succ_from_nfUDecorRightPred (z := z) hz))

def coreNFOfTarget : CoreKernelTarget -> NormalForm V
  | .nfXASqRightPred => nfXASqRightPred
  | .nfUSqLiftRightSPred => nfUSqLiftRightSPred
  | .nfXADecorRightPred => nfXADecorRightPred
  | .nfUDecorLiftRightSPred => nfUDecorLiftRightSPred
  | .nfXADecorLeftPred => nfXADecorLeftPred
  | .nfUDecorLiftLeftSPred => nfUDecorLiftLeftSPred
  | .nfUStablePred => nfUStablePred
  | .nfUHolePred => nfUHolePred
  | .nfUDecorHolePred => nfUDecorHolePred
  | .nfXASqAPred => nfXASqAPred
  | .nfUSqLiftAPred => nfUSqLiftAPred
  | .nfUDecorRightPred => nfUDecorRightPred

theorem corePurifiedRow_certificate_of_target
    (tg : CoreKernelTarget) :
    PurifiedCtxRowCertificate ctxNFOfTag
      (coreNFOfTarget tg) (corePurifiedRowOfTarget tg) := by
  cases tg with
  | nfXASqRightPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfXASqRightPred
  | nfUSqLiftRightSPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUSqLiftRightSPred
  | nfXADecorRightPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfXADecorRightPred
  | nfUDecorLiftRightSPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUDecorLiftRightSPred
  | nfXADecorLeftPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfXADecorLeftPred
  | nfUDecorLiftLeftSPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUDecorLiftLeftSPred
  | nfUStablePred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUStablePred
  | nfUHolePred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUHolePred
  | nfUDecorHolePred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUDecorHolePred
  | nfXASqAPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfXASqAPred
  | nfUSqLiftAPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUSqLiftAPred
  | nfUDecorRightPred =>
      simpa [coreNFOfTarget, corePurifiedRowOfTarget] using rowCert_nfUDecorRightPred

end CorePurifiedContextRows

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
