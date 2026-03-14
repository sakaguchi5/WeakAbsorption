import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Closure
open WeakAbsorption.Closure
namespace WeakAbsorption
/-! ############################################################
## Equational theory: RedEq
############################################################ -/
/-- Equational closure of rewriting. -/
abbrev RedEq {α} : Term α → Term α → Prop :=
  WeakAbsorption.Closure.EqvGen (@Red α)
------------------------------------------------------------
-- Fundamental structure lemmas (EqvGen itself)
------------------------------------------------------------
/-- EqvGen の冪等性（flatten）：
    いったん同値閉包した関係を、さらに同値閉包しても何も増えない。 -/
theorem EqvGen_idem {α : Type} {r : α → α → Prop} {x y : α} :
  EqvGen (EqvGen r) x y → EqvGen r x y := by
  intro h
  induction h with
  | rel a b hab =>
      -- hab : EqvGen r a b
      exact hab
  | refl a =>
      exact EqvGen.refl a
  | symm a b _ ih =>
      exact EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ =>
      exact EqvGen.trans _ _ _ ih₁ ih₂

/-- あなたの `Red` 用にそのまま特化した形（欲しい型そのもの）。 -/
theorem RedEq_idem {α : Type} {t u : Term α} :
  EqvGen (EqvGen (@Red α)) t u → EqvGen (@Red α) t u :=
by
  exact EqvGen_idem (r := @Red α)
------------------------------------------------------------
-- Congruence lemmas (compatibility with op)
------------------------------------------------------------
theorem RedEq_op_left {α : Type}
  (t₂ : Term α) {t₁ t₁' : Term α} :
  RedEq t₁ t₁' →
  RedEq (Term.op t₁ t₂) (Term.op t₁' t₂) := by
  intro h
  induction h with
  | rel x y hRed =>
      exact EqvGen.rel _ _ (Red.left _ _ _ hRed)
  | refl x =>
      exact EqvGen.refl _
  | symm _ _ _ ih =>
      exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact EqvGen.trans _ _ _ ih₁ ih₂
theorem RedEq_op_right {α : Type}
  (t₁ : Term α) {t₂ t₂' : Term α} :
  RedEq t₂ t₂' →
  RedEq (Term.op t₁ t₂) (Term.op t₁ t₂') := by
  intro h
  induction h with
  | rel x y hRed =>
      exact EqvGen.rel _ _ (Red.right _ _ _ hRed)
  | refl x =>
      exact EqvGen.refl _
  | symm _ _ _ ih =>
      exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact EqvGen.trans _ _ _ ih₁ ih₂
------------------------------------------------------------
-- Quotient bridge lemmas
------------------------------------------------------------
theorem RedEq.sound_step {α}
  {x y : Term α} (h : RedStep x y) :
  Quot.mk RedEq x = Quot.mk RedEq y := by
  exact Quot.sound (EqvGen.rel _ _ (Red.step _ _ h))

theorem RedEq_ctx {t u : Term α} (C : Ctx α) :
  RedEq t u → RedEq (Ctx.plug C t) (Ctx.plug C u) := by
  intro h
  induction C with
  | hole =>
      simpa [Ctx.plug] using h
  | left C r ih =>
      -- ih : RedEq (Ctx.plug C t) (Ctx.plug C u)
      -- RedEq_op_left の引数は (r : Term α) (h : RedEq ...)
      exact RedEq_op_left r ih
  | right l C ih =>
      -- RedEq_op_right の引数は (l : Term α) (h : RedEq ...)
      exact RedEq_op_right l ih


end WeakAbsorption
