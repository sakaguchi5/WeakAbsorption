import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Rows

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

section CoreRowFamilyTheorems

/-- (1) `x⋆Q` core-family rows are right-pure in the audited cases. -/
theorem xStarQ_family_right_purity :
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXASqRightPred z → z = nfXA) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXADecorRightPred z → z = nfXA) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXADecorLeftPred z → z = nfXA) ∧
    ChannelPure purifiedCtxProfile_nfXASqAPred_sqAbsorb.toCtxProfile := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact NFStepR_from_nfXASqRightPred_eq_nfXA (z := z) hz
  · intro z hz
    exact NFStepR_from_nfXADecorRightPred_eq_nfXA (z := z) hz
  · intro z hz
    exact NFStepR_from_nfXADecorLeftPred_eq_nfXA (z := z) hz
  · exact purifiedCtxProfile_nfXASqAPred_sqAbsorb_right_pure

/-- (2) `X⋆s` core-family rows are non-right in the audited cases; the only branching audited
cell is the left-pure lift of `AA`-branching. -/
theorem XMulS_family_nonright_purity :
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUSqLiftRightSPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorLiftRightSPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorLiftLeftSPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUStablePred z → z = nfU) ∧
    ChannelPure purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.toCtxProfile := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact NFStepR_from_nfUSqLiftRightSPred_eq_nfU (z := z) hz
  · intro z hz
    exact NFStepR_from_nfUDecorLiftRightSPred_eq_nfU (z := z) hz
  · intro z hz
    exact NFStepR_from_nfUDecorLiftLeftSPred_eq_nfU (z := z) hz
  · intro z hz
    exact NFStepR_from_nfUStablePred_eq_nfU (z := z) hz
  · exact purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb_left_pure

/-- (3) The hole-family audited context rows are root-pure: the only nonempty cells are root cells. -/
theorem hole_family_root_purity :
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUHolePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUHolePred z) ∧
    (∀ {z : NormalForm V}, ¬ NFDecorStepCtx (α := V) nfUHolePred z) ∧
    (∀ {z : NormalForm V}, NFC2C1StepCtx (α := V) nfUHolePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUDecorHolePred z → z = nfUHolePred) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUDecorHolePred z) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorHolePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUDecorHolePred z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sqAbsorb_succ_from_nfUHolePred_eq_nfU (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUHolePred (z := z) hz
  · intro z hz
    exact no_decor_succ_from_nfUHolePred (z := z) hz
  · intro z hz
    exact c2c1_succ_from_nfUHolePred_eq_nfU (z := z) hz
  · intro z hz
    exact sqAbsorb_succ_from_nfUDecorHolePred_eq_nfUHolePred (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUDecorHolePred (z := z) hz
  · intro z hz
    exact decor_succ_from_nfUDecorHolePred_eq_nfU (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUDecorHolePred (z := z) hz

/-- (4) `AA`-branching theorem: the audited branching profile on `nfXASqAPred` is right-pure
with exactly two exits. -/
theorem AA_branching_theorem :
    purifiedCtxProfile_nfXASqAPred_sqAbsorb.channel? = some .right ∧
    purifiedCtxProfile_nfXASqAPred_sqAbsorb.tags = [.nfXA, .nfXASqRightPred] := by
  simp [purifiedCtxProfile_nfXASqAPred_sqAbsorb]

/-- (5) Lifted `AA`-branching theorem: the audited branching profile on `nfUSqLiftAPred`
is the left-lift of the `AA` branching cell. -/
theorem lifted_AA_branching_theorem :
    purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.channel? = some .left ∧
    purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.tags = [.nfU, .nfUSqLiftRightPred] := by
  simp [purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb]

/-- (6) Re-audited `uDecorRightPred × Decor`: it is right-only singleton, not genuinely mixed. -/
theorem uDecorRightPred_decor_right_only_singleton_theorem :
    purifiedCtxProfile_nfUDecorRightPred_decor.channel? = some .right ∧
    purifiedCtxProfile_nfUDecorRightPred_decor.tags = [.nfU] := by
  simp [purifiedCtxProfile_nfUDecorRightPred_decor]

/-- (7) Core-row channel purity theorem on the currently audited prototype cells. -/
theorem core_row_channel_purity_theorem :
    ChannelPure purifiedCtxProfile_nfXASqAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.toCtxProfile ∧
    ChannelPure purifiedCtxProfile_nfUDecorRightPred_decor.toCtxProfile := by
  exact corePurifiedProfiles_no_genuine_mixed_proto

/-- (8) Core-row branching isolation theorem on the currently audited prototype cells. -/
theorem core_row_branching_isolation_theorem :
    purifiedCtxProfile_nfXASqAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUSqLiftAPred_sqAbsorb.tags.length = 2 ∧
    purifiedCtxProfile_nfUDecorRightPred_decor.tags.length = 1 := by
  exact purifiedCtxProfile_branching_cardinalities

end CoreRowFamilyTheorems

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
