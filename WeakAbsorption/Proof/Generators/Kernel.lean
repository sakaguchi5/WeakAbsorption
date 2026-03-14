import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Equational
import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Spec.Rule

open WeakAbsorption.Closure

namespace WeakAbsorption
namespace WAA
variable {α : Type}

open WeakAbsorption.Spec

/-- tag ごとの step（具体定義は NormalFormGenerators 側）。 -/
def step : RuleId → NormalForm α → NormalForm α → Prop
  | RuleId.SqAbsorb => NFSqStepCtx
  | RuleId.SqStable => NFSqStableStepCtx
  | RuleId.C2C1     => NFC2C1StepCtx
  | RuleId.Decor    => NFDecorStepCtx
  | RuleId.DoubleSq => NFDoubleSqStepCtx

theorem step_sound :
  ∀ tag {x y : NormalForm α},
  step (α := α) tag x y → NFRel (α := α) x y
  | RuleId.SqAbsorb, _x, _y, h => NFSqStepCtx_imp_NFRel (α := α) h
  | RuleId.SqStable, _x, _y, h => NFSqStableStepCtx_imp_NFRel (α := α) h
  | RuleId.C2C1,     _x, _y, h => NFC2C1StepCtx_imp_NFRel (α := α) h
  | RuleId.Decor,    _x, _y, h => NFDecorStepCtx_imp_NFRel (α := α) h
  | RuleId.DoubleSq, _x, _y, h => NFDoubleSqStepCtx_imp_NFRel (α := α) h

/-- ルール集合 R の下での1ステップ（有効化されたtagだけ使える）。 -/
def NFStepR (R : RuleSet) (x y : NormalForm α) : Prop :=
  ∃ tag, tag ∈ R ∧ step (α := α) tag x y

/-- R による反射対称推移閉包。 -/
def NFEqR (R : RuleSet) (x y : NormalForm α) : Prop :=
  EqvGen (NFStepR (α := α) R) x y

/-- Soundness: NFEqR R ⊆ NFRel -/
theorem NFEqR_imp_NFRel (R : RuleSet) {x y : NormalForm α} :
  NFEqR (α := α) R x y → NFRel (α := α) x y := by
  intro h
  induction h with
  | rel a b hab =>
      rcases hab with ⟨tag, _hin, hstep⟩
      exact step_sound (α := α) tag hstep
  | refl a =>
      exact EqvGen.refl (r := @Red α) a.1
  | symm a b _ ih =>
      exact EqvGen.symm (r := @Red α) _ _ ih
  | trans a b c _ _ ih₁ ih₂ =>
      exact EqvGen.trans (r := @Red α) _ _ _ ih₁ ih₂

/-- 旧API互換：デフォルトルール（現状5本全部）での NFEq -/
abbrev NFEq (x y : NormalForm α) : Prop :=
  NFEqR (α := α) Spec.defaultRules x y

theorem NFEq_imp_NFRel {x y : NormalForm α} :
  NFEq (α := α) x y → NFRel (α := α) x y :=
by
  intro h
  exact NFEqR_imp_NFRel (α := α) Spec.defaultRules h

theorem NFEq_imp_RedEq {x y : NormalForm α} :
  NFEq (α := α) x y → RedEq (α := α) x.1 y.1 :=
by
  intro h
  exact NFEq_imp_NFRel (α := α) h

end WAA
end WeakAbsorption
