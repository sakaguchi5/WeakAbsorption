import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Core
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Kernel_AA

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

section ContextProfilePrototypes

/-- The first genuine branching profile: `SqAbsorb` on `nfXASqAPred` has two right-channel exits. -/
def ctxCellProfile_nfXASqAPred_sqAbsorb : CtxProfile :=
  ctxProfile_nfXASqAPred_sqAbsorb

theorem ctxCellProfileCert_nfXASqAPred_sqAbsorb_public :
    CtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFSqStepCtx (α := V) src z)
      nfXASqAPred
      ctxCellProfile_nfXASqAPred_sqAbsorb :=
  ctxProfileCert_nfXASqAPred_sqAbsorb

/-- The lifted branching profile: `SqAbsorb` on `nfUSqLiftAPred` has two left-channel exits. -/
def ctxCellProfile_nfUSqLiftAPred_sqAbsorb : CtxProfile :=
  ctxProfile_nfUSqLiftAPred_sqAbsorb

theorem ctxCellProfileCert_nfUSqLiftAPred_sqAbsorb_public :
    CtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFSqStepCtx (α := V) src z)
      nfUSqLiftAPred
      ctxCellProfile_nfUSqLiftAPred_sqAbsorb :=
  ctxProfileCert_nfUSqLiftAPred_sqAbsorb

/-- Re-audited prototype: `Decor` on `nfUDecorRightPred` is not genuinely mixed;
it has a single right-channel exit to `nfU`. -/
def ctxCellProfile_nfUDecorRightPred_decor : CtxProfile :=
  ctxProfile_nfUDecorRightPred_decor

theorem ctxCellProfileCert_nfUDecorRightPred_decor_public :
    CtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFDecorStepCtx (α := V) src z)
      nfUDecorRightPred
      ctxCellProfile_nfUDecorRightPred_decor :=
  ctxProfileCert_nfUDecorRightPred_decor

end ContextProfilePrototypes

section PurifiedContextProfiles

def purifiedCtxProfile_nfXASqAPred_sqAbsorb : PurifiedCtxProfile :=
  { channel? := some .right, tags := [.nfXA, .nfXASqRightPred] }

theorem purifiedCtxProfileCert_nfXASqAPred_sqAbsorb :
    PurifiedCtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFSqStepCtx (α := V) src z)
      nfXASqAPred
      purifiedCtxProfile_nfXASqAPred_sqAbsorb := by
  refine ⟨?_, ?_⟩
  · simpa [PurifiedCtxProfile.toCtxProfile, purifiedCtxProfile_nfXASqAPred_sqAbsorb] using
      ctxProfileCert_nfXASqAPred_sqAbsorb
  · simp [purifiedCtxProfile_nfXASqAPred_sqAbsorb]

def purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb : PurifiedCtxProfile :=
  { channel? := some .left, tags := [.nfU, .nfUSqLiftRightPred] }

theorem purifiedCtxProfileCert_nfUSqLiftAPred_sqAbsorb :
    PurifiedCtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFSqStepCtx (α := V) src z)
      nfUSqLiftAPred
      purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb := by
  refine ⟨?_, ?_⟩
  · simpa [PurifiedCtxProfile.toCtxProfile, purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb] using
      ctxProfileCert_nfUSqLiftAPred_sqAbsorb
  · simp [purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb]

def purifiedCtxProfile_nfUDecorRightPred_decor : PurifiedCtxProfile :=
  { channel? := some .right, tags := [.nfU] }

theorem purifiedCtxProfileCert_nfUDecorRightPred_decor :
    PurifiedCtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFDecorStepCtx (α := V) src z)
      nfUDecorRightPred
      purifiedCtxProfile_nfUDecorRightPred_decor := by
  refine ⟨?_, ?_⟩
  · simpa [PurifiedCtxProfile.toCtxProfile, purifiedCtxProfile_nfUDecorRightPred_decor] using
      ctxProfileCert_nfUDecorRightPred_decor
  · simp [purifiedCtxProfile_nfUDecorRightPred_decor]

theorem purifiedCtxProfile_nfXASqAPred_sqAbsorb_right_pure :
    ChannelPure purifiedCtxProfile_nfXASqAPred_sqAbsorb.toCtxProfile := by
  apply purifiedProfile_channelPure
  simp [purifiedCtxProfile_nfXASqAPred_sqAbsorb]

theorem purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb_left_pure :
    ChannelPure purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.toCtxProfile := by
  apply purifiedProfile_channelPure
  simp [purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb]

theorem purifiedCtxProfile_nfUDecorRightPred_decor_right_pure :
    ChannelPure purifiedCtxProfile_nfUDecorRightPred_decor.toCtxProfile := by
  apply purifiedProfile_channelPure
  simp [purifiedCtxProfile_nfUDecorRightPred_decor]

/-- The only audited branching profiles currently fixed in Lean are AA-branching and its left lift. -/
theorem purifiedCtxProfile_branching_cardinalities :
    purifiedCtxProfile_nfXASqAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUDecorRightPred_decor.tags.length = 1 := by
  simp [purifiedCtxProfile_nfXASqAPred_sqAbsorb,
        purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb,
        purifiedCtxProfile_nfUDecorRightPred_decor]

/-- Current Lean-fixed prototype profiles exhibit no genuine mixed-channel branching. -/
theorem corePurifiedProfiles_no_genuine_mixed_proto :
    ChannelPure purifiedCtxProfile_nfXASqAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUDecorRightPred_decor.toCtxProfile := by
  exact ⟨purifiedCtxProfile_nfXASqAPred_sqAbsorb_right_pure,
    purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb_left_pure,
    purifiedCtxProfile_nfUDecorRightPred_decor_right_pure⟩

end PurifiedContextProfiles

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
