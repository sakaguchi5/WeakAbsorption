import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Equational
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Proof.Generators.Kernel

import WeakAbsorption.Spec.Rule   -- ← 追加

open WeakAbsorption.Closure
open WeakAbsorption.Spec          -- ← 追加（RuleId / defaultRules 用）

namespace WeakAbsorption
namespace WAA

variable {α : Type}
--SqAbsorb
theorem NFSqStepCtx_imp_NFEq
  {x y : NormalForm α}
  (h : NFSqStepCtx (α := α) x y) :
  NFEq (α := α) x y := by
  apply EqvGen.rel
  refine ⟨RuleId.SqAbsorb, ?hin, h⟩
  simp [defaultRules]
--SqStable
theorem NFSqStableStepCtx_imp_NFEq
  {x y : NormalForm α}
  (h : NFSqStableStepCtx (α := α) x y) :
  NFEq (α := α) x y := by
  apply EqvGen.rel
  refine ⟨RuleId.SqStable, ?hin, h⟩
  simp [defaultRules]
--C2C1
theorem NFC2C1StepCtx_imp_NFEq
  {x y : NormalForm α}
  (h : NFC2C1StepCtx (α := α) x y) :
  NFEq (α := α) x y := by
  apply EqvGen.rel
  refine ⟨RuleId.C2C1, ?hin, h⟩
  simp [defaultRules]
--Decor
theorem NFDecorStepCtx_imp_NFEq
  {x y : NormalForm α}
  (h : NFDecorStepCtx (α := α) x y) :
  NFEq (α := α) x y := by
  apply EqvGen.rel
  refine ⟨RuleId.Decor, ?hin, h⟩
  simp [defaultRules]
--DoubleSq
theorem NFDoubleSqStepCtx_imp_NFEq
  {x y : NormalForm α}
  (h : NFDoubleSqStepCtx (α := α) x y) :
  NFEq (α := α) x y := by
  apply EqvGen.rel
  refine ⟨RuleId.DoubleSq, ?hin, h⟩
  simp [defaultRules]
--kernel soundness の sanity check
theorem NFEq_sound
  {x y : NormalForm α}
  (h : NFEq (α := α) x y) :
  NFRel (α := α) x y :=
by
  exact NFEq_imp_NFRel (α := α) h

end WAA
end WeakAbsorption
