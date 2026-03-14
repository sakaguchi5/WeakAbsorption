import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Models

namespace R3M4

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA

/-
A 4-element algebra M4 such that:
  - SqAbsorb, SqStable, Decor identities hold (so every step in R3 preserves eval)
  - but C2C1 equation can fail for suitable term substitution (used in Necessity/C2C1.lean)
-/

inductive M4 where
  | m0 | m1 | m2 | m3
  deriving DecidableEq, Repr

/-- Operation table (row a, col b):
  0: [0,0,0,0]
  1: [1,0,1,1]
  2: [2,2,0,1]
  3: [2,0,0,0]
-/
def mul : M4 → M4 → M4
  | .m0, _    => .m0
  | .m1, .m0  => .m1
  | .m1, .m1  => .m0
  | .m1, .m2  => .m1
  | .m1, .m3  => .m1
  | .m2, .m0  => .m2
  | .m2, .m1  => .m2
  | .m2, .m2  => .m0
  | .m2, .m3  => .m1
  | .m3, .m0  => .m2
  | .m3, .m1  => .m0
  | .m3, .m2  => .m0
  | .m3, .m3  => .m0

/-- evaluation of terms into M4 -/
def eval {α : Type} (ρ : α → M4) : Term α → M4
  | .var a   => ρ a
  | .op t u  => mul (eval ρ t) (eval ρ u)

/-- eval respects plugging a one-hole context -/
theorem eval_ctx_congr {α : Type} (ρ : α → M4) :
  ∀ (C : Ctx α) {t u : Term α},
    eval ρ t = eval ρ u →
    eval ρ (Ctx.plug C t) = eval ρ (Ctx.plug C u) := by
  intro C
  induction C with
  | hole =>
      intro t u h
      simpa [Ctx.plug] using h
  | left C r ih =>
      intro t u h
      simpa [Ctx.plug, eval] using congrArg (fun z => mul z (eval ρ r)) (ih (t := t) (u := u) h)
  | right l C ih =>
      intro t u h
      simpa [Ctx.plug, eval] using congrArg (fun z => mul (eval ρ l) z) (ih (t := t) (u := u) h)

/-- SqAbsorb identity: (a*b)*(b*b) = a*b -/
theorem sqAbsorb_mul : ∀ a b : M4, mul (mul a b) (mul b b) = mul a b := by
  intro a b; cases a <;> cases b <;> rfl

/-- SqStable identity: ((a*b)*(b*b))*b = (a*b)*(b*b) -/
theorem sqStable_mul :
  ∀ a b : M4, mul (mul (mul a b) (mul b b)) b = mul (mul a b) (mul b b) := by
  intro a b; cases a <;> cases b <;> rfl

/-- Decor identity: (a*b)*(b*(b*b)) = a*b -/
theorem decor_mul :
  ∀ a b : M4, mul (mul a b) (mul b (mul b b)) = mul a b := by
  intro a b; cases a <;> cases b <;> rfl

/-- NFSqStepCtx preserves eval -/
theorem eval_preserved_NFSqStepCtx {α : Type} (ρ : α → M4) {x y : NormalForm α} :
  NFSqStepCtx (α := α) x y → eval ρ x.1 = eval ρ y.1 := by
  rintro ⟨C, t, u, hx, hy⟩
  rw [hx, hy]
  apply eval_ctx_congr (ρ := ρ) C
  simp [eval, sqAbsorb_mul]

/-- NFSqStableStepCtx preserves eval -/
theorem eval_preserved_NFSqStableStepCtx {α : Type} (ρ : α → M4) {x y : NormalForm α} :
  NFSqStableStepCtx (α := α) x y → eval ρ x.1 = eval ρ y.1 := by
  rintro ⟨C, t, u, hx, hy⟩
  rw [hx, hy]
  apply eval_ctx_congr (ρ := ρ) C
  simp [eval, sqStable_mul]

/-- NFDecorStepCtx preserves eval -/
theorem eval_preserved_NFDecorStepCtx {α : Type} (ρ : α → M4) {x y : NormalForm α} :
  NFDecorStepCtx (α := α) x y → eval ρ x.1 = eval ρ y.1 := by
  rintro ⟨C, t, u, hx, hy⟩
  rw [hx, hy]
  apply eval_ctx_congr (ρ := ρ) C
  simp [eval, decor_mul]

abbrev R3 : RuleSet := Vars1.R3

/-- For R3, every NFStepR preserves eval. -/
theorem eval_preserved_NFStepR_R3 {α : Type} (ρ : α → M4) {x y : NormalForm α} :
  NFStepR (α := α) R3 x y → eval ρ x.1 = eval ρ y.1 := by
  rintro ⟨tag, hmem, hstep⟩
  have ht : tag = RuleId.SqAbsorb ∨ tag = RuleId.SqStable ∨ tag = RuleId.Decor := by
    simpa [R3] using hmem
  cases ht with
  | inl h =>
      subst h
      exact eval_preserved_NFSqStepCtx (ρ := ρ) hstep
  | inr ht =>
      cases ht with
      | inl h =>
          subst h
          exact eval_preserved_NFSqStableStepCtx (ρ := ρ) hstep
      | inr h =>
          subst h
          exact eval_preserved_NFDecorStepCtx (ρ := ρ) hstep

/-- Main invariant: NFEqR R3 implies eval equality. -/
theorem eval_eq_of_NFEqR_R3 {α : Type} (ρ : α → M4) {x y : NormalForm α} :
  NFEqR (α := α) R3 x y → eval ρ x.1 = eval ρ y.1 := by
  intro h
  induction h with
  | rel a b hab =>
      exact eval_preserved_NFStepR_R3 (ρ := ρ) hab
  | refl a =>
      rfl
  | symm a b _ ih =>
      exact ih.symm
  | trans a b c _ _ ih1 ih2 =>
      exact Eq.trans ih1 ih2

end R3M4

end Models
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
