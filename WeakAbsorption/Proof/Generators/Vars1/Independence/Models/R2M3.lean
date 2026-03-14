import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Core.Measure
import WeakAbsorption.Tooling.SmallCheck.Phase0
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Models

namespace R2M3

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.Closure
open WeakAbsorption.WAA
open WeakAbsorption.SmallCheck   -- brings V := Fin 1

/-
A 3-element algebra (M3) witnessing:
- SqAbsorb and SqStable equations hold (for all a,b)
- but the “Decor witness” terms (s vs D) can be separated for some valuation,
  hence R2 := {SqAbsorb,SqStable} is incomplete for NFRel.
-/

inductive M3 where
  | m0 | m1 | m2
  deriving DecidableEq, Repr

/-- operation table on M3:
row a, col b:
  0*0=0 0*1=0 0*2=0
  1*0=0 1*1=1 1*2=1
  2*0=0 2*1=0 2*2=1
-/
def mul : M3 → M3 → M3
  | M3.m0, _      => M3.m0
  | M3.m1, M3.m0  => M3.m0
  | M3.m1, M3.m1  => M3.m1
  | M3.m1, M3.m2  => M3.m1
  | M3.m2, M3.m0  => M3.m0
  | M3.m2, M3.m1  => M3.m0
  | M3.m2, M3.m2  => M3.m1

/-- evaluation of vars=1 terms into M3 -/
def eval (ρ : V → M3) : Term V → M3
  | .var a   => ρ a
  | .op t u  => mul (eval ρ t) (eval ρ u)

/-- evaluation respects plugging a one-hole context -/
theorem eval_ctx_congr (ρ : V → M3) :
  ∀ (C : Ctx V) {t u : Term V},
    eval ρ t = eval ρ u →
    eval ρ (Ctx.plug C t) = eval ρ (Ctx.plug C u) := by
  intro C
  induction C with
  | hole =>
      intro t u h
      simpa [Ctx.plug] using h
  | left C r ih =>
      intro t u h
      -- plug (left C r) t = (plug C t) ⋆ r
      -- eval is homomorphic
      simpa [Ctx.plug, eval] using congrArg (fun z => mul z (eval ρ r)) (ih (t := t) (u := u) h)
  | right l C ih =>
      intro t u h
      -- plug (right l C) t = l ⋆ (plug C t)
      simpa [Ctx.plug, eval] using congrArg (fun z => mul (eval ρ l) z) (ih (t := t) (u := u) h)

/-- SqAbsorb identity in M3: (a*b)*(b*b) = a*b -/
theorem sqAbsorb_mul : ∀ a b : M3, mul (mul a b) (mul b b) = mul a b := by
  intro a b
  cases a <;> cases b <;> rfl

/-- SqStable identity in M3: ((a*b)*(b*b))*b = (a*b)*(b*b) -/
theorem sqStable_mul :
  ∀ a b : M3, mul (mul (mul a b) (mul b b)) b = mul (mul a b) (mul b b) := by
  intro a b
  cases a <;> cases b <;> rfl

/-- NFSqStepCtx preserves eval (because SqAbsorb holds and contexts are congruences). -/
theorem eval_preserved_NFSqStepCtx (ρ : V → M3) {x y : NormalForm V} :
  NFSqStepCtx (α := V) x y → eval ρ x.1 = eval ρ y.1 := by
  rintro ⟨C, t, u, hx, hy⟩
  -- rewrite x,y into a common context
  rw [hx, hy]
  -- reduce to the root identity inside the hole, then lift by context congruence
  apply eval_ctx_congr (ρ := ρ) C
  -- root identity:
  -- eval (((t⋆u)⋆(u⋆u))) = eval (t⋆u)
  -- becomes sqAbsorb_mul with a:=eval t, b:=eval u
  simp [eval, sqAbsorb_mul]

/-- NFSqStableStepCtx preserves eval (because SqStable holds and contexts are congruences). -/
theorem eval_preserved_NFSqStableStepCtx (ρ : V → M3) {x y : NormalForm V} :
  NFSqStableStepCtx (α := V) x y → eval ρ x.1 = eval ρ y.1 := by
  rintro ⟨C, t, u, hx, hy⟩
  rw [hx, hy]
  apply eval_ctx_congr (ρ := ρ) C
  simp [eval, sqStable_mul]

/-- For R2 = [SqAbsorb,SqStable], every NFStepR preserves eval. -/
theorem eval_preserved_NFStepR_R2 (ρ : V → M3) {x y : NormalForm V} :
  NFStepR (α := V) Vars1.R2 x y →
    eval ρ x.1 = eval ρ y.1 := by
  rintro ⟨tag, hmem, hstep⟩
  have : tag = RuleId.SqAbsorb ∨ tag = RuleId.SqStable := by
    simpa using hmem
  cases this with
  | inl h =>
      subst h
      -- step SqAbsorb = NFSqStepCtx
      exact eval_preserved_NFSqStepCtx (ρ := ρ) (by simpa [WAA.step] using hstep)
  | inr h =>
      subst h
      -- step SqStable = NFSqStableStepCtx
      exact eval_preserved_NFSqStableStepCtx (ρ := ρ) (by simpa [WAA.step] using hstep)

/-- Main invariant: NFEqR R2 implies eval equality. -/
theorem eval_eq_of_NFEqR_R2 (ρ : V → M3) {x y : NormalForm V} :
  NFEqR (α := V) Vars1.R2 x y →
    eval ρ x.1 = eval ρ y.1 := by
  intro h
  induction h with
  | rel a b hab =>
      exact eval_preserved_NFStepR_R2 (ρ := ρ) hab
  | refl a =>
      rfl
  | symm a b _ ih =>
      exact ih.symm
  | trans a b c _ _ ih1 ih2 =>
      exact Eq.trans ih1 ih2

end R2M3

end Models
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
