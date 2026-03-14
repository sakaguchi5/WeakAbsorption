import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_KernelTheorems
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_RootCells

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

section RootBehaviorRows

/-!
This section packages the root-behavior cells into row-wise certificates.
These rows are the canonical theorem-level counterpart of `ProofCore_R4Registry`: each
`NoRoot` target is exposed as a single `NoRootRow`, so the file structure is driven by
registry rows rather than by discovery order. Productive rows (`uHolePred`,
`uDecorHolePred`) are intentionally left at the cell level for now, since their step
outputs are not uniform enough to fit the current `NoRootRow` record.
-/

def rootNoRootRow_xASqAPred : NoRootRow xASqAPredTerm where
  sqAbsorb := fun t u => rootCell_xASqAPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_xASqAPred_sqStable_noRoot t u
  decor := fun t u => rootCell_xASqAPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_xASqAPred_c2c1_noRoot x0 p z0

def rootNoRootRow_xASqRightPred : NoRootRow xASqRightSPredTerm where
  sqAbsorb := fun t u => rootCell_xASqRightPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_xASqRightPred_sqStable_noRoot t u
  decor := fun t u => rootCell_xASqRightPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_xASqRightPred_c2c1_noRoot x0 p z0

def rootNoRootRow_xAStablePred : NoRootRow xAStablePredTerm where
  sqAbsorb := fun t u => rootCell_xAStablePred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_xAStablePred_sqStable_noRoot t u
  decor := fun t u => rootCell_xAStablePred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_xAStablePred_c2c1_noRoot x0 p z0

def rootNoRootRow_xADecorAPred : NoRootRow xADecorAPredTerm where
  sqAbsorb := fun t u => rootCell_xADecorAPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_xADecorAPred_sqStable_noRoot t u
  decor := fun t u => rootCell_xADecorAPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_xADecorAPred_c2c1_noRoot x0 p z0

def rootNoRootRow_xADecorLeftPred : NoRootRow xADecorLeftSPredTerm where
  sqAbsorb := fun t u => rootCell_xADecorLeftPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_xADecorLeftPred_sqStable_noRoot t u
  decor := fun t u => rootCell_xADecorLeftPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_xADecorLeftPred_c2c1_noRoot x0 p z0

def rootNoRootRow_xADecorRightPred : NoRootRow xADecorRightSPredTerm where
  sqAbsorb := fun t u => rootCell_xADecorRightPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_xADecorRightPred_sqStable_noRoot t u
  decor := fun t u => rootCell_xADecorRightPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_xADecorRightPred_c2c1_noRoot x0 p z0

def rootNoRootRow_uSqLiftAPred : NoRootRow uSqLiftAPredTerm where
  sqAbsorb := fun t u => rootCell_uSqLiftAPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_uSqLiftAPred_sqStable_noRoot t u
  decor := fun t u => rootCell_uSqLiftAPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_uSqLiftAPred_c2c1_noRoot x0 p z0

def rootNoRootRow_uSqLiftRightPred : NoRootRow uSqLiftRightSPredTerm where
  sqAbsorb := fun t u => rootCell_uSqLiftRightPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_uSqLiftRightPred_sqStable_noRoot t u
  decor := fun t u => rootCell_uSqLiftRightPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_uSqLiftRightPred_c2c1_noRoot x0 p z0

def rootNoRootRow_uDecorLiftLeftPred : NoRootRow uDecorLiftLeftSPredTerm where
  sqAbsorb := fun t u => rootCell_uDecorLiftLeftPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_uDecorLiftLeftPred_sqStable_noRoot t u
  decor := fun t u => rootCell_uDecorLiftLeftPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_uDecorLiftLeftPred_c2c1_noRoot x0 p z0

def rootNoRootRow_uDecorLiftRightPred : NoRootRow uDecorLiftRightSPredTerm where
  sqAbsorb := fun t u => rootCell_uDecorLiftRightPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_uDecorLiftRightPred_sqStable_noRoot t u
  decor := fun t u => rootCell_uDecorLiftRightPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_uDecorLiftRightPred_c2c1_noRoot x0 p z0

def rootNoRootRow_uDecorRightPred : NoRootRow uDecorRightPredTerm where
  sqAbsorb := fun t u => rootCell_uDecorRightPred_sqAbsorb_noRoot t u
  sqStable := fun t u => rootCell_uDecorRightPred_sqStable_noRoot t u
  decor := fun t u => rootCell_uDecorRightPred_decor_noRoot t u
  c2c1 := fun x0 p z0 => rootCell_uDecorRightPred_c2c1_noRoot x0 p z0

def rootNoRootRow_uStablePred : NoRootRow uStablePredTerm where
  sqAbsorb := by
    intro t u hEq
    exact rootCell_uStablePred_sqAbsorb_noRoot hEq
  sqStable := by
    intro t u hEq
    exact rootCell_uStablePred_sqStable_noRoot hEq
  decor := by
    intro t u hEq
    exact rootCell_uStablePred_decor_noRoot hEq
  c2c1 := by
    intro x0 p z0 hEq
    exact rootCell_uStablePred_c2c1_noRoot hEq

/-- `uHolePred` is the first genuinely mixed row: two productive root cells and two no-root cells. -/
def rootMixedRow_uHolePred :
    MixedRootRow
      (SqAbsorbProductiveGoal uHolePredTerm uTerm)
      (SqStableNoRootGoal uHolePredTerm)
      (DecorNoRootGoal uHolePredTerm)
      (C2C1ProductiveGoal uHolePredTerm uTerm) where
  sqAbsorb := by
    intro t u hEq
    exact rootCell_uHolePred_sqAbsorb_productive hEq
  sqStable := by
    intro t u
    exact rootCell_uHolePred_sqStable_noRoot t u
  decor := by
    intro t u
    exact rootCell_uHolePred_decor_noRoot t u
  c2c1 := by
    intro x0 p z0 hEq
    exact rootCell_uHolePred_c2c1_productive hEq

/-- `uDecorHolePred` is the second mixed row: only `Decor` is productive at root. -/
def rootMixedRow_uDecorHolePred :
    MixedRootRow
      (SqAbsorbNoRootGoal uDecorHolePredTerm)
      (SqStableNoRootGoal uDecorHolePredTerm)
      (DecorProductiveGoal uDecorHolePredTerm uTerm)
      (C2C1NoRootGoal uDecorHolePredTerm) where
  sqAbsorb := by
    intro t u
    exact rootCell_uDecorHolePred_sqAbsorb_noRoot t u
  sqStable := by
    intro t u
    exact rootCell_uDecorHolePred_sqStable_noRoot t u
  decor := by
    intro t u hEq
    exact rootCell_uDecorHolePred_decor_productive hEq
  c2c1 := by
    intro x0 p z0
    exact rootCell_uDecorHolePred_c2c1_noRoot x0 p z0

section RootBehaviorRegistryBridge

/-!
This is the registry-facing theorem bridge: it turns a `RootTarget` directly into the
row certificate expected by `ProofCore_R4Registry.rootRowView`. From this point on, the
registry is not merely metadata; it has a canonical theorem-level payload.
-/

def rootRowCertificate : (tg : RootTarget) -> TargetRowCertificate tg
  | .xASqAPred        => rootNoRootRow_xASqAPred
  | .xASqRightPred    => rootNoRootRow_xASqRightPred
  | .xAStablePred     => rootNoRootRow_xAStablePred
  | .xADecorAPred     => rootNoRootRow_xADecorAPred
  | .xADecorLeftPred  => rootNoRootRow_xADecorLeftPred
  | .xADecorRightPred => rootNoRootRow_xADecorRightPred
  | .uSqLiftAPred     => rootNoRootRow_uSqLiftAPred
  | .uSqLiftRightPred => rootNoRootRow_uSqLiftRightPred
  | .uDecorLiftLeftPred  => rootNoRootRow_uDecorLiftLeftPred
  | .uDecorLiftRightPred => rootNoRootRow_uDecorLiftRightPred
  | .uDecorRightPred  => rootNoRootRow_uDecorRightPred
  | .uStablePred      => rootNoRootRow_uStablePred
  | .uHolePred        => rootMixedRow_uHolePred
  | .uDecorHolePred   => rootMixedRow_uDecorHolePred

end RootBehaviorRegistryBridge


section PlugBehaviorRegistryBridge

/-!
Registry-facing theorem bridge for explicit `plug_eq_*_lhs_cases` decompositions.
This is the plug-level analogue of `rootRowCertificate`.
-/

def plugLhsRowCertificate : (tg : PlugMainTarget) -> PlugLhsRowCertificate tg
  | .xAStablePred        => plug_eq_xAStablePred_lhs_cases
  | .uStablePred         => plug_eq_uStablePred_lhs_cases
  | .uHolePred           => plug_eq_uHolePred_lhs_cases
  | .uDecorHolePred      => plug_eq_uDecorHolePred_lhs_cases
  | .m                   => plug_eq_m_lhs_cases
  | .uDecorRightPred     => plug_eq_uDecorRightPred_lhs_cases
  | .xASqRightPred       => plug_eq_xASqRightPred_lhs_cases
  | .uSqLiftRightPred    => plug_eq_uSqLiftRightPred_lhs_cases
  | .xADecorRightPred    => plug_eq_xADecorRightPred_lhs_cases
  | .uDecorLiftRightPred => plug_eq_uDecorLiftRightPred_lhs_cases
  | .xASqAPred           => plug_eq_xASqAPred_lhs_cases
  | .uSqLiftAPred        => plug_eq_uSqLiftAPred_lhs_cases
  | .xADecorLeftPred     => plug_eq_xADecorLeftPred_lhs_cases
  | .uDecorLiftLeftPred  => plug_eq_uDecorLiftLeftPred_lhs_cases

/-- Registry-facing theorem payload for reusable rhs plug-decomposition rows. -/
def plugRhsRowCertificate : (tg : PlugRhsTarget) -> PlugRhsRowCertificate tg
  | .sA  => plug_eq_sA_rhs_cases
  | .sv  => plug_eq_sv_rhs_cases
  | .ssv => plug_eq_ssv_rhs_cases
  | .svs => plug_eq_svs_rhs_cases
  | .AA  => plug_eq_AA_rhs_cases

end PlugBehaviorRegistryBridge

section ContextBehaviorRows

/-!
A first batch of context-step rows, built from already explicit per-rule successor/no-successor
lemmas. This is the context-step analogue of `RootBehaviorRows`, but we only package rows whose
four rule-cells already have stable direct theorem forms.
-/

def contextRow_nfUStablePred :
    MixedRootRow
      (SqAbsorbCtxEqGoal nfUStablePred nfU)
      (SqStableCtxEqGoal nfUStablePred nfU)
      (DecorCtxEqGoal nfUStablePred nfU)
      (C2C1CtxEqGoal nfUStablePred nfU) where
  sqAbsorb := by
    intro z hz
    exact sqAbsorb_step_from_nfUStablePred_eq_nfU (z := z) hz
  sqStable := by
    intro z hz
    exact sqStable_step_from_nfUStablePred_eq_nfU (z := z) hz
  decor := by
    intro z hz
    exact decor_step_from_nfUStablePred_eq_nfU (z := z) hz
  c2c1 := by
    intro z hz
    exact c2c1_step_from_nfUStablePred_eq_nfU (z := z) hz

/-- `uHolePred` is mixed at context-step level: SqAbsorb/C2C1 reach `nfU`, the other two have no step. -/
def contextRow_nfUHolePred :
    MixedRootRow
      (SqAbsorbCtxEqGoal nfUHolePred nfU)
      (SqStableCtxNoStepGoal nfUHolePred)
      (DecorCtxNoStepGoal nfUHolePred)
      (C2C1CtxEqGoal nfUHolePred nfU) where
  sqAbsorb := by
    intro z hz
    exact sqAbsorb_succ_from_nfUHolePred_eq_nfU (z := z) hz
  sqStable := by
    intro z hz
    exact no_sqStable_succ_from_nfUHolePred (z := z) hz
  decor := by
    intro z hz
    exact no_decor_succ_from_nfUHolePred (z := z) hz
  c2c1 := by
    intro z hz
    exact c2c1_succ_from_nfUHolePred_eq_nfU (z := z) hz

/-- `uDecorHolePred` is mixed at context-step level: SqAbsorb reaches `nfUHolePred`, Decor reaches `nfU`, the other two have no step. -/
def contextRow_nfUDecorHolePred :
    MixedRootRow
      (SqAbsorbCtxEqGoal nfUDecorHolePred nfUHolePred)
      (SqStableCtxNoStepGoal nfUDecorHolePred)
      (DecorCtxEqGoal nfUDecorHolePred nfU)
      (C2C1CtxNoStepGoal nfUDecorHolePred) where
  sqAbsorb := by
    intro z hz
    exact sqAbsorb_succ_from_nfUDecorHolePred_eq_nfUHolePred (z := z) hz
  sqStable := by
    intro z hz
    exact no_sqStable_succ_from_nfUDecorHolePred (z := z) hz
  decor := by
    intro z hz
    exact decor_succ_from_nfUDecorHolePred_eq_nfU (z := z) hz
  c2c1 := by
    intro z hz
    exact no_c2c1_succ_from_nfUDecorHolePred (z := z) hz

end ContextBehaviorRows

end RootBehaviorRows




end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
