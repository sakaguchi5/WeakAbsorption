import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.TwoPointComponent
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step14
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Patterns
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Registry
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Targets
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4PlugRegistry
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4Mechanisms
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore_R4KernelRegistry

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

/-
We first record that the previous "nfV is isolated" route is false:
there is an incoming R4-step into nfV, namely
  x ⋆ A  ->  x ⋆ s
by SqAbsorb inside the context (x ⋆ □).
-/

private theorem x_normal : Normal (α := V) x := by
  intro u hu
  nomatch hu

private theorem s_normal : Normal (α := V) s := by
  apply (Normal_op_iff (α := V) x x).2
  refine ⟨x_normal, x_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    cases hw
  · simp [IsC2pRoot, x]

private theorem A_normal : Normal (α := V) A := by
  apply (Normal_op_iff (α := V) s s).2
  refine ⟨s_normal, s_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    dsimp [s, x] at hw
    nomatch hw
  · dsimp [IsC2pRoot, s, x]
    rintro ⟨w, hw⟩
    injection hw with h1 h2
    cases h1

private theorem xA_normal : Normal (α := V) (x.op A) := by
  apply (Normal_op_iff (α := V) x A).2
  refine ⟨x_normal, A_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    cases hw
  · cases A <;> simp [IsC2pRoot, x]

def nfXA : NormalForm V := ⟨xATerm, xA_normal⟩

theorem nfXA_ne_nfV : nfXA.1 ≠ nfV.1 := by
  intro hEq
  dsimp [nfXA, nfV, xATerm, vTerm, x, s, A] at hEq
  nomatch hEq

theorem nfU_ne_nfXA : nfU.1 ≠ nfXA.1 := by
  intro hEq
  dsimp [nfU, nfXA, uTerm, xATerm, x, s, A] at hEq
  nomatch hEq

/--
`nfV = x ⋆ s` has an incoming R4-step:
  x ⋆ A  ->  x ⋆ s
by SqAbsorb under the context `(x ⋆ □)`.
So the "nfV is isolated" route is dead.
-/

theorem plug_eq_x_cases
    (C : Ctx V) (t : Term V)
    (h : Ctx.plug C t = x) :
    C = Ctx.hole ∧ t = x := by
  induction C generalizing t with
  | hole =>
      constructor
      · rfl
      · simpa [Ctx.plug] using h
  | left C r ih =>
      simp [Ctx.plug, x] at h
  | right l C ih =>
      simp [Ctx.plug, x] at h

theorem plug_eq_s_cases
    (C : Ctx V) (t : Term V)
    (h : Ctx.plug C t = s) :
    (C = Ctx.hole ∧ t = s) ∨
    (C = Ctx.left Ctx.hole x ∧ t = x) ∨
    (C = Ctx.right x Ctx.hole ∧ t = x) := by
  induction C generalizing t with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r ih =>
      cases r with
      | var a =>
          dsimp [Ctx.plug, s, x] at h
          injection h with hL hR
          cases hR
          rcases plug_eq_x_cases C t hL with ⟨rfl, rfl⟩
          exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      | op r1 r2 =>
          dsimp [Ctx.plug, s, x] at h
          injection h with hL hR
          cases hR
  | right l C ih =>
      cases l with
      | var a =>
          dsimp [Ctx.plug, s, x] at h
          injection h with hL hR
          cases hL
          rcases plug_eq_x_cases C t hR with ⟨rfl, rfl⟩
          exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      | op l1 l2 =>
          dsimp [Ctx.plug, s, x] at h
          injection h with hL hR
          cases hL

theorem plug_eq_xs_cases
    (C : Ctx V) (t : Term V)
    (h : Ctx.plug C t = vTerm) :
    (C = Ctx.hole ∧ t = vTerm) ∨
    (C = Ctx.left Ctx.hole s ∧ t = x) ∨
    (C = Ctx.right x Ctx.hole ∧ t = s) ∨
    (C = Ctx.right x (Ctx.left Ctx.hole x) ∧ t = x) ∨
    (C = Ctx.right x (Ctx.right x Ctx.hole) ∧ t = x) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r =>
      dsimp [Ctx.plug, vTerm, s, x] at h
      injection h with hL hR
      subst hR
      rcases plug_eq_x_cases C t hL with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | right l C =>
      dsimp [Ctx.plug, vTerm, s, x] at h
      injection h with hL hR
      subst hL
      rcases plug_eq_s_cases C t hR with hC | hC | hC
      · rcases hC with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · rcases hC with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · rcases hC with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

theorem no_plug_sqAbsorb_lhs_eq_vTerm
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C (((t.op u).op (u.op u))) ≠ vTerm := by
  intro h
  rcases plug_eq_xs_cases C (((t.op u).op (u.op u))) h with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

theorem no_plug_sqStable_lhs_eq_vTerm
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((((t.op u).op (u.op u)).op u)) ≠ vTerm := by
  intro h
  rcases plug_eq_xs_cases C ((((t.op u).op (u.op u)).op u)) h with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

theorem no_plug_decor_lhs_eq_vTerm
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((t.op u).op (u.op (u.op u))) ≠ vTerm := by
  intro h
  rcases plug_eq_xs_cases C ((t.op u).op (u.op (u.op u))) h with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

theorem no_plug_c2c1_lhs_eq_vTerm
    (C : Ctx V) (x0 p z : Term V) :
    Ctx.plug C (((x0.op (p.op z)).op z).op (p.op z)) ≠ vTerm := by
  intro h
  rcases plug_eq_xs_cases C (((x0.op (p.op z)).op z).op (p.op z)) h with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

theorem no_NFStepR_from_nfV {z : NormalForm V} :
    ¬ NFStepR (α := V) R4 nfV z := by
  intro h
  rcases h with ⟨tag, htag, hstep⟩
  have htag' :
      tag = RuleId.SqAbsorb ∨
      tag = RuleId.SqStable ∨
      tag = RuleId.Decor ∨
      tag = RuleId.C2C1 := by
    simpa [R4] using htag
  rcases htag' with rfl | rfl | rfl | rfl
  · rcases (show NFSqStepCtx (α := V) nfV z from hstep) with
      ⟨C, t, u, hx, hz⟩
    exact no_plug_sqAbsorb_lhs_eq_vTerm C t u (by
      simpa [nfV] using hx.symm)
  · rcases (show NFSqStableStepCtx (α := V) nfV z from hstep) with
      ⟨C, t, u, hx, hz⟩
    exact no_plug_sqStable_lhs_eq_vTerm C t u (by
      simpa [nfV] using hx.symm)
  · rcases (show NFDecorStepCtx (α := V) nfV z from hstep) with
      ⟨C, t, u, hx, hz⟩
    exact no_plug_decor_lhs_eq_vTerm C t u (by
      simpa [nfV] using hx.symm)
  · rcases (show NFC2C1StepCtx (α := V) nfV z from hstep) with
      ⟨C, x0, p, z0, hx, hz⟩
    exact no_plug_c2c1_lhs_eq_vTerm C x0 p z0 (by
      simpa [nfV] using hx.symm)

def vSqHolePredTerm : Term V := vTerm.op A
def vDecorHolePredTerm : Term V := vTerm.op (s.op A)
def vDecorRightPredTerm : Term V := x.op (s.op vTerm)

private theorem no_plug_sqStable_rhs_eq_vTerm
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C (((t.op u).op (u.op u))) ≠ vTerm := by
  intro h
  rcases plug_eq_xs_cases C (((t.op u).op (u.op u))) h with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

private theorem no_plug_c2c1_rhs_eq_vTerm
    (C : Ctx V) (x0 p z0 : Term V) :
    Ctx.plug C (((x0.op (p.op z0)).op z0)) ≠ vTerm := by
  intro h
  rcases plug_eq_xs_cases C (((x0.op (p.op z0)).op z0)) h with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

private theorem no_sqStable_pred_to_nfV {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) z nfV := by
  rintro ⟨C, t, u, hz, hv⟩
  exact no_plug_sqStable_rhs_eq_vTerm C t u (by
    simpa [nfV] using hv.symm)

private theorem no_c2c1_pred_to_nfV {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) z nfV := by
  rintro ⟨C, x0, p, z0, hz, hv⟩
  exact no_plug_c2c1_rhs_eq_vTerm C x0 p z0 (by
    simpa [nfV] using hv.symm)

private theorem sqAbsorb_pred_to_nfV_term_cases {z : NormalForm V} :
    NFSqStepCtx (α := V) z nfV →
      z.1 = vSqHolePredTerm ∨ z.1 = nfXA.1 := by
  rintro ⟨C, t, u, hz, hv⟩
  have hv' : Ctx.plug C (t.op u) = vTerm := by
    simpa [nfV] using hv.symm
  rcases plug_eq_xs_cases C (t.op u) hv' with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with ht hu
    subst ht
    subst hu
    left
    simpa [vSqHolePredTerm, vTerm, A, s, x] using hz
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with ht hu
    subst ht
    subst hu
    right
    simpa [nfXA, xATerm, A, s, x] using hz
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

private theorem decor_pred_to_nfV_term_cases {z : NormalForm V} :
    NFDecorStepCtx (α := V) z nfV →
      z.1 = vDecorHolePredTerm ∨ z.1 = vDecorRightPredTerm := by
  rintro ⟨C, t, u, hz, hv⟩
  have hv' : Ctx.plug C (t.op u) = vTerm := by
    simpa [nfV] using hv.symm
  rcases plug_eq_xs_cases C (t.op u) hv' with
    h0 | h1 | h2 | h3 | h4
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [vTerm, s, x] at hEq
    injection hEq with ht hu
    subst ht
    subst hu
    left
    simpa [vDecorHolePredTerm, vTerm, A, s, x] using hz
  · rcases h1 with ⟨_, hEq⟩
    cases hEq
  · rcases h2 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with ht hu
    subst ht
    subst hu
    right
    simpa [vDecorRightPredTerm, vTerm, A, s, x] using hz
  · rcases h3 with ⟨_, hEq⟩
    cases hEq
  · rcases h4 with ⟨_, hEq⟩
    cases hEq

theorem NFStepR_to_nfV_term_cases {z : NormalForm V} :
    NFStepR (α := V) R4 z nfV →
      z.1 = vSqHolePredTerm ∨
      z.1 = nfXA.1 ∨
      z.1 = vDecorHolePredTerm ∨
      z.1 = vDecorRightPredTerm := by
  intro h
  rcases h with ⟨tag, htag, hstep⟩
  have htag' :
      tag = RuleId.SqAbsorb ∨
      tag = RuleId.SqStable ∨
      tag = RuleId.Decor ∨
      tag = RuleId.C2C1 := by
    simpa [R4] using htag
  rcases htag' with rfl | rfl | rfl | rfl
  ·
    rcases sqAbsorb_pred_to_nfV_term_cases
      (z := z) (show NFSqStepCtx (α := V) z nfV from hstep) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  ·
    exact False.elim <|
      no_sqStable_pred_to_nfV (z := z)
        (show NFSqStableStepCtx (α := V) z nfV from hstep)
  ·
    rcases decor_pred_to_nfV_term_cases
      (z := z) (show NFDecorStepCtx (α := V) z nfV from hstep) with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  ·
    exact False.elim <|
      no_c2c1_pred_to_nfV (z := z)
        (show NFC2C1StepCtx (α := V) z nfV from hstep)

theorem x_normal_from_nfV : Normal (α := V) x :=
  ((Normal_op_iff (α := V) x s).1 nfV.2).1

theorem s_normal_from_nfV : Normal (α := V) s :=
  ((Normal_op_iff (α := V) x s).1 nfV.2).2.1

theorem A_normal_from_nfXA : Normal (α := V) A :=
  ((Normal_op_iff (α := V) x A).1 nfXA.2).2.1

theorem sA_normal : Normal (α := V) (s.op A) := by
  apply (Normal_op_iff (α := V) s A).2
  refine ⟨s_normal_from_nfV, A_normal_from_nfXA, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    dsimp [s, A, x] at hw
    injection hw with h1 h2
    cases h2
  · dsimp [IsC2pRoot, s, A, x]
    rintro ⟨w, hw⟩
    injection hw with h1 h2
    cases h1

private theorem sv_normal : Normal (α := V) (s.op vTerm) := by
  apply (Normal_op_iff (α := V) s vTerm).2
  refine ⟨s_normal_from_nfV, nfV.2, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    dsimp [s, vTerm, x] at hw
    injection hw with h1 h2
    cases h2
  · dsimp [IsC2pRoot, s, vTerm, x]
    rintro ⟨w, hw⟩
    injection hw with h1 h2
    cases h1

private theorem vSqHolePred_normal : Normal (α := V) vSqHolePredTerm := by
  apply (Normal_op_iff (α := V) vTerm A).2
  refine ⟨nfV.2, A_normal_from_nfXA, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    dsimp [vSqHolePredTerm, vTerm, A, s, x] at hw
    injection hw with h1 h2
    cases h2
  · dsimp [IsC2pRoot, vSqHolePredTerm, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    injection hw with h1 h2
    cases h1

private theorem vDecorHolePred_normal : Normal (α := V) vDecorHolePredTerm := by
  apply (Normal_op_iff (α := V) vTerm (s.op A)).2
  refine ⟨nfV.2, sA_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    dsimp [vDecorHolePredTerm, vTerm, A, s, x] at hw
    injection hw with h1 h2
    cases h2
  · dsimp [IsC2pRoot, vDecorHolePredTerm, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    injection hw with h1 h2
    cases h1

private theorem vDecorRightPred_normal : Normal (α := V) vDecorRightPredTerm := by
  apply (Normal_op_iff (α := V) x (s.op vTerm)).2
  refine ⟨x_normal_from_nfV, sv_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩
    cases hw
  · dsimp [IsC2pRoot, vDecorRightPredTerm, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    cases hw

def nfVSqHolePred : NormalForm V := ⟨vSqHolePredTerm, vSqHolePred_normal⟩
def nfVDecorHolePred : NormalForm V := ⟨vDecorHolePredTerm, vDecorHolePred_normal⟩
def nfVDecorRightPred : NormalForm V := ⟨vDecorRightPredTerm, vDecorRightPred_normal⟩

theorem nfVSqHolePred_steps_to_nfV :
    NFStepR (α := V) R4 nfVSqHolePred nfV := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  · refine ⟨Ctx.hole, x, s, ?_, ?_⟩
    · change vSqHolePredTerm = Ctx.plug Ctx.hole (((x.op s).op (s.op s)))
      simp [Ctx.plug, vSqHolePredTerm, vTerm, A, s, x]
    · change vTerm = Ctx.plug Ctx.hole (x.op s)
      simp [Ctx.plug, vTerm, s, x]

theorem nfVDecorHolePred_steps_to_nfV :
    NFStepR (α := V) R4 nfVDecorHolePred nfV := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  · refine ⟨Ctx.hole, x, s, ?_, ?_⟩
    · change vDecorHolePredTerm = Ctx.plug Ctx.hole ((x.op s).op (s.op (s.op s)))
      simp [Ctx.plug, vDecorHolePredTerm, vTerm, A, s, x]
    · change vTerm = Ctx.plug Ctx.hole (x.op s)
      simp [Ctx.plug, vTerm, s, x]

theorem nfVDecorRightPred_steps_to_nfV :
    NFStepR (α := V) R4 nfVDecorRightPred nfV := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  · refine ⟨Ctx.right x Ctx.hole, x, x, ?_, ?_⟩
    · change vDecorRightPredTerm
        = Ctx.plug (Ctx.right x Ctx.hole) ((x.op x).op (x.op (x.op x)))
      simp [Ctx.plug, vDecorRightPredTerm, vTerm, s, x]
    · change vTerm = Ctx.plug (Ctx.right x Ctx.hole) (x.op x)
      simp [Ctx.plug, vTerm, s, x]

theorem NFStepR_to_nfV_cases {z : NormalForm V} :
    NFStepR (α := V) R4 z nfV →
      z = nfVSqHolePred ∨
      z = nfXA ∨
      z = nfVDecorHolePred ∨
      z = nfVDecorRightPred := by
  intro h
  rcases NFStepR_to_nfV_term_cases (z := z) h with h | h | h | h
  · left
    apply Subtype.ext
    simpa using h
  · right
    left
    apply Subtype.ext
    simpa using h
  · right
    right
    left
    apply Subtype.ext
    simpa using h
  · right
    right
    right
    apply Subtype.ext
    simpa using h

theorem NFStepR_to_nfV_iff :
    ∀ z : NormalForm V,
      NFStepR (α := V) R4 z nfV ↔
        z = nfVSqHolePred ∨
        z = nfXA ∨
        z = nfVDecorHolePred ∨
        z = nfVDecorRightPred := by
  intro z
  constructor
  · intro h
    exact NFStepR_to_nfV_cases (z := z) h
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact nfVSqHolePred_steps_to_nfV
    · exact nfXA_steps_to_nfV
    · exact nfVDecorHolePred_steps_to_nfV
    · exact nfVDecorRightPred_steps_to_nfV

private theorem nfVSqHolePred_ne_nfXA :
    nfVSqHolePred ≠ nfXA := by
  intro h
  have h' : nfVSqHolePred.1 = nfXA.1 := congrArg Subtype.val h
  dsimp [nfVSqHolePred, nfXA, vSqHolePredTerm, xATerm, vTerm, A, s, x] at h'
  injection h' with h1 h2
  cases h1

private theorem nfVDecorHolePred_ne_nfXA :
    nfVDecorHolePred ≠ nfXA := by
  intro h
  have h' : nfVDecorHolePred.1 = nfXA.1 := congrArg Subtype.val h
  dsimp [nfVDecorHolePred, nfXA, vDecorHolePredTerm, xATerm, vTerm, A, s, x] at h'
  injection h' with h1 h2
  cases h1

private theorem nfVDecorRightPred_ne_nfXA :
    nfVDecorRightPred ≠ nfXA := by
  intro h
  have h' : nfVDecorRightPred.1 = nfXA.1 := congrArg Subtype.val h
  dsimp [nfVDecorRightPred, nfXA, vDecorRightPredTerm, xATerm, vTerm, A, s, x] at h'
  injection h' with h1 h2
  cases h2

private theorem nfVSqHolePred_ne_nfVDecorHolePred :
    nfVSqHolePred ≠ nfVDecorHolePred := by
  intro h
  have h' : nfVSqHolePred.1 = nfVDecorHolePred.1 := congrArg Subtype.val h
  dsimp [nfVSqHolePred, nfVDecorHolePred, vSqHolePredTerm, vDecorHolePredTerm, vTerm, A, s, x] at h'
  injection h' with h1 h2
  cases h2

private theorem nfVSqHolePred_ne_nfVDecorRightPred :
    nfVSqHolePred ≠ nfVDecorRightPred := by
  intro h
  have h' : nfVSqHolePred.1 = nfVDecorRightPred.1 := congrArg Subtype.val h
  dsimp [nfVSqHolePred, nfVDecorRightPred, vSqHolePredTerm, vDecorRightPredTerm, vTerm, A, s, x] at h'
  injection h' with h1 h2
  cases h1

private theorem nfVDecorHolePred_ne_nfVDecorRightPred :
    nfVDecorHolePred ≠ nfVDecorRightPred := by
  intro h
  have h' : nfVDecorHolePred.1 = nfVDecorRightPred.1 := congrArg Subtype.val h
  dsimp [nfVDecorHolePred, nfVDecorRightPred, vDecorHolePredTerm, vDecorRightPredTerm, vTerm, A, s, x] at h'
  injection h' with h1 h2
  cases h1

theorem NFAdjR_at_nfV_iff
    (z : NormalForm V) :
    NFAdjR (α := V) R4 nfV z ↔
      z = nfVSqHolePred ∨
      z = nfXA ∨
      z = nfVDecorHolePred ∨
      z = nfVDecorRightPred := by
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (no_NFStepR_from_nfV (z := z) h)
    · exact NFStepR_to_nfV_cases (z := z) h
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact Or.inr nfVSqHolePred_steps_to_nfV
    · exact Or.inr nfXA_steps_to_nfV
    · exact Or.inr nfVDecorHolePred_steps_to_nfV
    · exact Or.inr nfVDecorRightPred_steps_to_nfV

theorem plug_eq_A_cases
    (C : Ctx V) (t : Term V)
    (h : Ctx.plug C t = A) :
    (C = Ctx.hole ∧ t = A) ∨
    (C = Ctx.left Ctx.hole s ∧ t = s) ∨
    (C = Ctx.right s Ctx.hole ∧ t = s) ∨
    (C = Ctx.left (Ctx.left Ctx.hole x) s ∧ t = x) ∨
    (C = Ctx.left (Ctx.right x Ctx.hole) s ∧ t = x) ∨
    (C = Ctx.right s (Ctx.left Ctx.hole x) ∧ t = x) ∨
    (C = Ctx.right s (Ctx.right x Ctx.hole) ∧ t = x) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r =>
      dsimp [Ctx.plug, A, s, x] at h
      injection h with hL hR
      subst hR
      rcases plug_eq_s_cases C t hL with h0 | h1 | h2
      · rcases h0 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · rcases h1 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · rcases h2 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  | right l C =>
      dsimp [Ctx.plug, A, s, x] at h
      injection h with hL hR
      subst hL
      rcases plug_eq_s_cases C t hR with h0 | h1 | h2
      · rcases h0 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · rcases h1 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
      · rcases h2 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))

private theorem plug_eq_xA_cases
    (C : Ctx V) (t : Term V)
    (h : Ctx.plug C t = xATerm) :
    (C = Ctx.hole ∧ t = xATerm) ∨
    (C = Ctx.left Ctx.hole A ∧ t = x) ∨
    (C = Ctx.right x Ctx.hole ∧ t = A) ∨
    (C = Ctx.right x (Ctx.left Ctx.hole s) ∧ t = s) ∨
    (C = Ctx.right x (Ctx.right s Ctx.hole) ∧ t = s) ∨
    (C = Ctx.right x (Ctx.left (Ctx.left Ctx.hole x) s) ∧ t = x) ∨
    (C = Ctx.right x (Ctx.left (Ctx.right x Ctx.hole) s) ∧ t = x) ∨
    (C = Ctx.right x (Ctx.right s (Ctx.left Ctx.hole x)) ∧ t = x) ∨
    (C = Ctx.right x (Ctx.right s (Ctx.right x Ctx.hole)) ∧ t = x) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r =>
      dsimp [Ctx.plug, xATerm, A, s, x] at h
      injection h with hL hR
      subst hR
      rcases plug_eq_x_cases C t hL with ⟨rfl, rfl⟩
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | right l C =>
      dsimp [Ctx.plug, xATerm, A, s, x] at h
      injection h with hL hR
      subst hL
      rcases plug_eq_A_cases C t hR with h0 | h1 | h2 | h3 | h4 | h5 | h6
      ·
        rcases h0 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      ·
        rcases h1 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      ·
        rcases h2 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      ·
        rcases h3 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
      ·
        rcases h4 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
      ·
        rcases h5 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))))
      ·
        rcases h6 with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))))


private theorem sqAbsorb_pred_to_nfXA_term_cases {z : NormalForm V} :
    NFSqStepCtx (α := V) z nfXA →
      z.1 = xASqHolePredTerm ∨
      z.1 = xASqAPredTerm ∨
      z.1 = xASqLeftSPredTerm ∨
      z.1 = xASqRightSPredTerm := by
  rintro ⟨C, t, u, hz, hxA⟩
  have hxA' : Ctx.plug C (t.op u) = xATerm := by
    simpa [nfXA] using hxA.symm
  rcases plug_eq_xA_cases C (t.op u) hxA' with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inl (by
      simpa [xASqHolePredTerm, xATerm, A, s, x, Ctx.plug] using hz)
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨hC, hEq⟩
    subst hC
    dsimp [A, s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inr (Or.inl (by
      simpa [xASqAPredTerm, xATerm, A, s, x, Ctx.plug] using hz))
  ·
    rcases h3 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inr (Or.inr (Or.inl (by
      simpa [xASqLeftSPredTerm, xATerm, A, s, x, Ctx.plug] using hz)))
  ·
    rcases h4 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inr (Or.inr (Or.inr (by
      simpa [xASqRightSPredTerm, xATerm, A, s, x, Ctx.plug] using hz)))
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq

private theorem sqStable_pred_to_nfXA_term_cases {z : NormalForm V} :
    NFSqStableStepCtx (α := V) z nfXA →
      z.1 = xAStablePredTerm := by
  rintro ⟨C, t, u, hz, hxA⟩
  have hxA' : Ctx.plug C ((t.op u).op (u.op u)) = xATerm := by
    simpa [nfXA] using hxA.symm
  rcases plug_eq_xA_cases C (((t.op u).op (u.op u))) hxA' with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨hC, hEq⟩
    subst hC
    dsimp [A, s, x] at hEq
    injection hEq with h1 h2
    have hu_eq : u = x := by
      injection h2 with hu1 hu2
    subst u
    have ht_eq : t = x := by
      dsimp [s, x] at h1
      injection h1 with ht1 ht2
    subst t
    simpa [xAStablePredTerm, xATerm, A, s, x, Ctx.plug] using hz
  ·
    rcases h3 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h4 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq
private theorem no_plug_c2c1_rhs_eq_xATerm
    (C : Ctx V) (x0 p z0 : Term V) :
    Ctx.plug C (((x0.op (p.op z0)).op z0)) ≠ xATerm := by
  intro h
  rcases plug_eq_xA_cases C (((x0.op (p.op z0)).op z0)) h with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨_, hEq⟩
    dsimp [A, s, x] at hEq
    injection hEq with hL hR
    subst z0
    injection hL with hx0 hp
    cases hp
  ·
    rcases h3 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h4 with ⟨_, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq

private theorem no_c2c1_pred_to_nfXA {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) z nfXA := by
  rintro ⟨C, x0, p, z0, hz, hxA⟩
  exact no_plug_c2c1_rhs_eq_xATerm C x0 p z0 (by
    simpa [nfXA] using hxA.symm)


private theorem decor_pred_to_nfXA_term_cases {z : NormalForm V} :
    NFDecorStepCtx (α := V) z nfXA →
      z.1 = xADecorHolePredTerm ∨
      z.1 = xADecorAPredTerm ∨
      z.1 = xADecorLeftSPredTerm ∨
      z.1 = xADecorRightSPredTerm := by
  rintro ⟨C, t, u, hz, hxA⟩
  have hxA' : Ctx.plug C (t.op u) = xATerm := by
    simpa [nfXA] using hxA.symm
  rcases plug_eq_xA_cases C (t.op u) hxA' with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inl (by
      simpa [xADecorHolePredTerm, xATerm, A, s, x, Ctx.plug] using hz)
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨hC, hEq⟩
    subst hC
    dsimp [A, s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inr (Or.inl (by
      simpa [xADecorAPredTerm, xATerm, A, s, x, Ctx.plug] using hz))
  ·
    rcases h3 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inr (Or.inr (Or.inl (by
      simpa [xADecorLeftSPredTerm, xATerm, A, s, x, Ctx.plug] using hz)))
  ·
    rcases h4 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with ht hu
    subst t
    subst u
    exact Or.inr (Or.inr (Or.inr (by
      simpa [xADecorRightSPredTerm, xATerm, A, s, x, Ctx.plug] using hz)))
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq

theorem NFStepR_to_nfXA_term_cases {z : NormalForm V} :
    NFStepR (α := V) R4 z nfXA →
      z.1 = xASqHolePredTerm ∨
      z.1 = xASqAPredTerm ∨
      z.1 = xASqLeftSPredTerm ∨
      z.1 = xASqRightSPredTerm ∨
      z.1 = xAStablePredTerm ∨
      z.1 = xADecorHolePredTerm ∨
      z.1 = xADecorAPredTerm ∨
      z.1 = xADecorLeftSPredTerm ∨
      z.1 = xADecorRightSPredTerm := by
  intro h
  rcases h with ⟨tag, htag, hstep⟩
  have htag' :
      tag = RuleId.SqAbsorb ∨
      tag = RuleId.SqStable ∨
      tag = RuleId.Decor ∨
      tag = RuleId.C2C1 := by
    simpa [R4] using htag
  rcases htag' with rfl | rfl | rfl | rfl
  ·
    rcases sqAbsorb_pred_to_nfXA_term_cases
      (z := z) (show NFSqStepCtx (α := V) z nfXA from hstep) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  ·
    rcases sqStable_pred_to_nfXA_term_cases
      (z := z) (show NFSqStableStepCtx (α := V) z nfXA from hstep) with h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  ·
    rcases decor_pred_to_nfXA_term_cases
      (z := z) (show NFDecorStepCtx (α := V) z nfXA from hstep) with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  ·
    exact False.elim <|
      no_c2c1_pred_to_nfXA (z := z)
        (show NFC2C1StepCtx (α := V) z nfXA from hstep)

private theorem sqAbsorb_succ_from_nfXA_eq_nfV {z : NormalForm V} :
    NFSqStepCtx (α := V) nfXA z → z = nfV := by
  rintro ⟨C, t, u, hxA, hz⟩
  have hxA' : Ctx.plug C (((t.op u).op (u.op u))) = xATerm := by
    simpa [nfXA] using hxA.symm
  rcases plug_eq_xA_cases C (((t.op u).op (u.op u))) hxA' with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨hC, hEq⟩
    subst hC
    dsimp [A, s, x] at hEq
    injection hEq with hL hR
    have hu : u = x := by
      injection hR with hu1 hu2
    subst u
    have ht : t = x := by
      dsimp [s, x] at hL
      injection hL with ht1 ht2
    subst t
    apply Subtype.ext
    simpa [nfV, vTerm, xATerm, A, s, x, Ctx.plug] using hz
  ·
    rcases h3 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h4 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq

theorem no_sqStable_succ_from_nfXA {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfXA z := by
  rintro ⟨C, t, u, hxA, hz⟩
  have hxA' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xATerm := by
    simpa [nfXA] using hxA.symm
  rcases plug_eq_xA_cases C ((((t.op u).op (u.op u)).op u)) hxA' with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨hC, hEq⟩
    subst hC
    dsimp [A, s, x] at hEq
    injection hEq with hL hR
    injection hL with hLL hLR
    cases hLL
  ·
    rcases h3 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h4 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq

theorem no_decor_succ_from_nfXA {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfXA z := by
  rintro ⟨C, t, u, hxA, hz⟩
  have hxA' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xATerm := by
    simpa [nfXA] using hxA.symm
  rcases plug_eq_xA_cases C ((t.op u).op (u.op (u.op u))) hxA' with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨hC, hEq⟩
    subst hC
    dsimp [A, s, x] at hEq
    injection hEq with hL hR
    cases hR
  ·
    rcases h3 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h4 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq

theorem no_c2c1_succ_from_nfXA {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfXA z := by
  rintro ⟨C, x0, p, z0, hxA, hz⟩
  have hxA' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xATerm := by
    simpa [nfXA] using hxA.symm
  rcases plug_eq_xA_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hxA' with
    h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [xATerm, A, s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨hC, hEq⟩
    subst hC
    dsimp [A, s, x] at hEq
    injection hEq with hL hR
    injection hL with hLL hLR
    cases hLL
  ·
    rcases h3 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h4 with ⟨hC, hEq⟩
    subst hC
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h5 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h6 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h7 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h8 with ⟨_, hEq⟩
    cases hEq

theorem NFStepR_from_nfXA_eq_nfV {z : NormalForm V} :
    NFStepR (α := V) R4 nfXA z → z = nfV := by
  intro h
  rcases h with ⟨tag, htag, hstep⟩
  have htag' :
      tag = RuleId.SqAbsorb ∨
      tag = RuleId.SqStable ∨
      tag = RuleId.Decor ∨
      tag = RuleId.C2C1 := by
    simpa [R4] using htag
  rcases htag' with rfl | rfl | rfl | rfl
  ·
    exact sqAbsorb_succ_from_nfXA_eq_nfV
      (z := z) (show NFSqStepCtx (α := V) nfXA z from hstep)
  ·
    exact False.elim <|
      no_sqStable_succ_from_nfXA (z := z)
        (show NFSqStableStepCtx (α := V) nfXA z from hstep)
  ·
    exact False.elim <|
      no_decor_succ_from_nfXA (z := z)
        (show NFDecorStepCtx (α := V) nfXA z from hstep)
  ·
    exact False.elim <|
      no_c2c1_succ_from_nfXA (z := z)
        (show NFC2C1StepCtx (α := V) nfXA z from hstep)

theorem NFAdjR_at_nfXA_term_cases {z : NormalForm V} :
    NFAdjR (α := V) R4 nfXA z →
      z = nfV ∨
      z.1 = xASqHolePredTerm ∨
      z.1 = xASqAPredTerm ∨
      z.1 = xASqLeftSPredTerm ∨
      z.1 = xASqRightSPredTerm ∨
      z.1 = xAStablePredTerm ∨
      z.1 = xADecorHolePredTerm ∨
      z.1 = xADecorAPredTerm ∨
      z.1 = xADecorLeftSPredTerm ∨
      z.1 = xADecorRightSPredTerm := by
  intro h
  rcases h with h | h
  ·
    left
    exact NFStepR_from_nfXA_eq_nfV (z := z) h
  ·
    right
    exact NFStepR_to_nfXA_term_cases (z := z) h

def wTerm : Term V := vTerm.op s

private theorem wTerm_not_normal :
    ¬ Normal (α := V) wTerm := by
  intro hN
  have hnoC1 : ¬ IsC1Root (α := V) vTerm s :=
    ((Normal_op_iff (α := V) vTerm s).1 hN).2.2.1
  apply hnoC1
  refine ⟨x, ?_⟩
  dsimp [wTerm, vTerm, s, x]

theorem no_plug_sqAbsorb_lhs_eq_s
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C (((t.op u).op (u.op u))) ≠ s := by
  intro h
  rcases plug_eq_s_cases C (((t.op u).op (u.op u))) h with h0 | h1 | h2
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨_, hEq⟩
    cases hEq

theorem no_plug_sqStable_lhs_eq_s
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((((t.op u).op (u.op u)).op u)) ≠ s := by
  intro h
  rcases plug_eq_s_cases C ((((t.op u).op (u.op u)).op u)) h with h0 | h1 | h2
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨_, hEq⟩
    cases hEq

theorem no_plug_decor_lhs_eq_s
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((t.op u).op (u.op (u.op u))) ≠ s := by
  intro h
  rcases plug_eq_s_cases C ((t.op u).op (u.op (u.op u))) h with h0 | h1 | h2
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨_, hEq⟩
    cases hEq

theorem no_plug_c2c1_lhs_eq_s
    (C : Ctx V) (x0 p z0 : Term V) :
    Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) ≠ s := by
  intro h
  rcases plug_eq_s_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) h with h0 | h1 | h2
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨_, hEq⟩
    cases hEq

theorem plug_sqAbsorb_lhs_eq_uTerm_cases
    (C : Ctx V) (t u : Term V)
    (h : Ctx.plug C (((t.op u).op (u.op u))) = uTerm) :
    (C = Ctx.hole ∧ (((t.op u).op (u.op u))) = uTerm) ∨
    ∃ C', C = Ctx.left C' s ∧ Ctx.plug C' (((t.op u).op (u.op u))) = xATerm := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hR
      exact Or.inr ⟨C, rfl, by simpa [xATerm] using hL⟩
  | right l C =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hL
      exact False.elim (no_plug_sqAbsorb_lhs_eq_s C t u hR)

theorem plug_sqStable_lhs_eq_uTerm_cases
    (C : Ctx V) (t u : Term V)
    (h : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uTerm) :
    (C = Ctx.hole ∧ ((((t.op u).op (u.op u)).op u)) = uTerm) ∨
    ∃ C', C = Ctx.left C' s ∧ Ctx.plug C' ((((t.op u).op (u.op u)).op u)) = xATerm := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hR
      exact Or.inr ⟨C, rfl, by simpa [xATerm] using hL⟩
  | right l C =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hL
      exact False.elim (no_plug_sqStable_lhs_eq_s C t u hR)

theorem plug_decor_lhs_eq_uTerm_cases
    (C : Ctx V) (t u : Term V)
    (h : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uTerm) :
    (C = Ctx.hole ∧ ((t.op u).op (u.op (u.op u))) = uTerm) ∨
    ∃ C', C = Ctx.left C' s ∧ Ctx.plug C' ((t.op u).op (u.op (u.op u))) = xATerm := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hR
      exact Or.inr ⟨C, rfl, by simpa [xATerm] using hL⟩
  | right l C =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hL
      exact False.elim (no_plug_decor_lhs_eq_s C t u hR)

theorem plug_c2c1_lhs_eq_uTerm_cases
    (C : Ctx V) (x0 p z0 : Term V)
    (h : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uTerm) :
    (C = Ctx.hole ∧ ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uTerm) ∨
    ∃ C', C = Ctx.left C' s ∧ Ctx.plug C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xATerm := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hR
      exact Or.inr ⟨C, rfl, by simpa [xATerm] using hL⟩
  | right l C =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hL
      exact False.elim (no_plug_c2c1_lhs_eq_s C x0 p z0 hR)

theorem no_sqAbsorb_root_eq_uTerm
    (t u : Term V) :
    (((t.op u).op (u.op u))) ≠ uTerm := by
  intro hEq
  dsimp [uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem no_sqStable_root_eq_uTerm
    (t u : Term V) :
    ((((t.op u).op (u.op u)).op u)) ≠ uTerm := by
  intro hEq
  dsimp [uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem no_decor_root_eq_uTerm
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uTerm := by
  intro hEq
  dsimp [uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem no_c2c1_root_eq_uTerm
    (x0 p z0 : Term V) :
    ((((x0.op (p.op z0)).op z0).op (p.op z0))) ≠ uTerm := by
  intro hEq
  dsimp [uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem no_sqAbsorb_succ_from_nfU {z : NormalForm V} :
    ¬ NFSqStepCtx (α := V) nfU z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uTerm := by
    simpa [nfU] using hx.symm
  rcases plug_sqAbsorb_lhs_eq_uTerm_cases C t u hx' with
    hroot | ⟨C', hC, hleft⟩
  ·
    rcases hroot with ⟨rfl, hEq⟩
    exact no_sqAbsorb_root_eq_uTerm t u hEq
  ·
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFSqStepCtx (α := V) nfXA y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXA] using hleft.symm
    have hyEq : y = nfV :=
      sqAbsorb_succ_from_nfXA_eq_nfV (z := y) hy
    have hyVal : y.1 = vTerm := by
      simpa [nfV] using congrArg Subtype.val hyEq
    have hzEq : z.1 = wTerm := by
      have : Ctx.plug C' (t.op u) = vTerm := hyVal
      rw [this] at hz'
      simpa [wTerm] using hz'
    have : Normal (α := V) wTerm := by
      simpa [hzEq] using z.2
    exact wTerm_not_normal this

theorem no_sqStable_succ_from_nfU {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfU z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uTerm := by
    simpa [nfU] using hx.symm
  rcases plug_sqStable_lhs_eq_uTerm_cases C t u hx' with
    hroot | ⟨C', hC, hleft⟩
  ·
    rcases hroot with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uTerm t u hEq
  ·
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
    have hy : NFSqStableStepCtx (α := V) nfXA y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXA] using hleft.symm
    exact no_sqStable_succ_from_nfXA (z := y) hy

theorem no_decor_succ_from_nfU {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfU z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uTerm := by
    simpa [nfU] using hx.symm
  rcases plug_decor_lhs_eq_uTerm_cases C t u hx' with
    hroot | ⟨C', hC, hleft⟩
  ·
    rcases hroot with ⟨rfl, hEq⟩
    exact no_decor_root_eq_uTerm t u hEq
  ·
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFDecorStepCtx (α := V) nfXA y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXA] using hleft.symm
    exact no_decor_succ_from_nfXA (z := y) hy

theorem no_c2c1_succ_from_nfU {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfU z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uTerm := by
    simpa [nfU] using hx.symm
  rcases plug_c2c1_lhs_eq_uTerm_cases C x0 p z0 hx' with
    hroot | ⟨C', hC, hleft⟩
  ·
    rcases hroot with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_uTerm x0 p z0 hEq
  ·
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
    have hy : NFC2C1StepCtx (α := V) nfXA y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfXA] using hleft.symm
    exact no_c2c1_succ_from_nfXA (z := y) hy

theorem no_NFStepR_from_nfU {z : NormalForm V} :
    ¬ NFStepR (α := V) R4 nfU z := by
  intro h
  rcases h with ⟨tag, htag, hstep⟩
  have htag' :
      tag = RuleId.SqAbsorb ∨
      tag = RuleId.SqStable ∨
      tag = RuleId.Decor ∨
      tag = RuleId.C2C1 := by
    simpa [R4] using htag
  rcases htag' with rfl | rfl | rfl | rfl
  ·
    exact no_sqAbsorb_succ_from_nfU (z := z)
      (show NFSqStepCtx (α := V) nfU z from hstep)
  ·
    exact no_sqStable_succ_from_nfU (z := z)
      (show NFSqStableStepCtx (α := V) nfU z from hstep)
  ·
    exact no_decor_succ_from_nfU (z := z)
      (show NFDecorStepCtx (α := V) nfU z from hstep)
  ·
    exact no_c2c1_succ_from_nfU (z := z)
      (show NFC2C1StepCtx (α := V) nfU z from hstep)




private inductive PredUTerm : Term V → Prop
  | hole : PredUTerm uHolePredTerm
  | sqLiftHole : PredUTerm uSqLiftHolePredTerm
  | sqLiftA : PredUTerm uSqLiftAPredTerm
  | sqLiftLeftS : PredUTerm uSqLiftLeftSPredTerm
  | sqLiftRightS : PredUTerm uSqLiftRightSPredTerm
  | sqRight : PredUTerm uSqRightPredTerm
  | stable : PredUTerm uStablePredTerm
  | decorHole : PredUTerm uDecorHolePredTerm
  | decorLiftHole : PredUTerm uDecorLiftHolePredTerm
  | decorLiftA : PredUTerm uDecorLiftAPredTerm
  | decorLiftLeftS : PredUTerm uDecorLiftLeftSPredTerm
  | decorLiftRightS : PredUTerm uDecorLiftRightSPredTerm
  | decorRight : PredUTerm uDecorRightPredTerm

private theorem plug_eq_uTerm_rhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uTerm) :
    (C = Ctx.hole ∧ r = uTerm) ∨
    (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xATerm) ∨
    (∃ C', C = Ctx.right xATerm C' ∧ Ctx.plug C' r = s) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r0 =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hR
      exact Or.inr (Or.inl ⟨C, rfl, by simpa [xATerm] using hL⟩)
  | right l C =>
      dsimp [Ctx.plug, uTerm] at h
      injection h with hL hR
      subst hL
      exact Or.inr (Or.inr ⟨C, rfl, by simpa using hR⟩)

private theorem no_plug_sqStable_rhs_eq_s
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C (((t.op u).op (u.op u))) ≠ s := by
  intro h
  rcases plug_eq_s_cases C (((t.op u).op (u.op u))) h with h0 | h1 | h2
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨_, hEq⟩
    cases hEq

private theorem no_plug_c2c1_rhs_eq_s
    (C : Ctx V) (x0 p z0 : Term V) :
    Ctx.plug C (((x0.op (p.op z0)).op z0)) ≠ s := by
  intro h
  rcases plug_eq_s_cases C (((x0.op (p.op z0)).op z0)) h with h0 | h1 | h2
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases h1 with ⟨_, hEq⟩
    cases hEq
  ·
    rcases h2 with ⟨_, hEq⟩
    cases hEq

private theorem no_sqStable_rhs_root_eq_uTerm
    (t u : Term V) :
    (((t.op u).op (u.op u))) ≠ uTerm := by
  intro hEq
  dsimp [uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

private theorem sqAbsorb_pred_to_nfU_isPred {z : NormalForm V} :
    NFSqStepCtx (α := V) z nfU → PredUTerm z.1 := by
  rintro ⟨C, t, u, hz, hu⟩
  have hu' : Ctx.plug C (t.op u) = uTerm := by
    simpa [nfU] using hu.symm
  rcases plug_eq_uTerm_rhs_cases C (t.op u) hu' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [uTerm] at hEq
    injection hEq with ht hu
    subst t
    subst u
    have : z.1 = uHolePredTerm := by
      simpa [uHolePredTerm, uTerm, xATerm, A, s, x, Ctx.plug] using hz
    simpa [this] using PredUTerm.hole
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    rcases plug_eq_xA_cases C' (t.op u) hleft with
      h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [xATerm] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uSqLiftHolePredTerm := by
        simpa [uSqLiftHolePredTerm, xASqHolePredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.sqLiftHole
    ·
      rcases h1 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h2 with ⟨hC', hEq⟩
      subst hC'
      dsimp [A, s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uSqLiftAPredTerm := by
        simpa [uSqLiftAPredTerm, xASqAPredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.sqLiftA
    ·
      rcases h3 with ⟨hC', hEq⟩
      subst hC'
      dsimp [s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uSqLiftLeftSPredTerm := by
        simpa [uSqLiftLeftSPredTerm, xASqLeftSPredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.sqLiftLeftS
    ·
      rcases h4 with ⟨hC', hEq⟩
      subst hC'
      dsimp [s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uSqLiftRightSPredTerm := by
        simpa [uSqLiftRightSPredTerm, xASqRightSPredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.sqLiftRightS
    ·
      rcases h5 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h6 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h7 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h8 with ⟨_, hEq⟩
      cases hEq
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_s_cases C' (t.op u) hright with h0 | h1 | h2
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uSqRightPredTerm := by
        simpa [uSqRightPredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.sqRight
    ·
      rcases h1 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h2 with ⟨_, hEq⟩
      cases hEq

private theorem sqStable_pred_to_nfU_isPred {z : NormalForm V} :
    NFSqStableStepCtx (α := V) z nfU → PredUTerm z.1 := by
  rintro ⟨C, t, u, hz, hu⟩
  have hu' : Ctx.plug C (((t.op u).op (u.op u))) = uTerm := by
    simpa [nfU] using hu.symm
  rcases plug_eq_uTerm_rhs_cases C (((t.op u).op (u.op u))) hu' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_sqStable_rhs_root_eq_uTerm t u hEq)
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    rcases plug_eq_xA_cases C' (((t.op u).op (u.op u))) hleft with
      h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [xATerm, A, s, x] at hEq
      injection hEq with hL hR
      cases hL
    ·
      rcases h1 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h2 with ⟨hC', hEq⟩
      subst hC'
      dsimp [A, s, x] at hEq
      injection hEq with h1 h2
      injection h2 with hu1 hu2
      subst u
      injection h1 with ht hu'
      subst t
      have : z.1 = uStablePredTerm := by
        simpa [uStablePredTerm, xAStablePredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.stable
    ·
      rcases h3 with ⟨hC', hEq⟩
      subst hC'
      dsimp [s, x] at hEq
      injection hEq with hL hR
      cases hL
    ·
      rcases h4 with ⟨hC', hEq⟩
      subst hC'
      dsimp [s, x] at hEq
      injection hEq with hL hR
      cases hL
    ·
      rcases h5 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h6 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h7 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h8 with ⟨_, hEq⟩
      cases hEq
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact False.elim (no_plug_sqStable_rhs_eq_s C' t u hright)

private theorem decor_pred_to_nfU_isPred {z : NormalForm V} :
    NFDecorStepCtx (α := V) z nfU → PredUTerm z.1 := by
  rintro ⟨C, t, u, hz, hu⟩
  have hu' : Ctx.plug C (t.op u) = uTerm := by
    simpa [nfU] using hu.symm
  rcases plug_eq_uTerm_rhs_cases C (t.op u) hu' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [uTerm] at hEq
    injection hEq with ht hu
    subst t
    subst u
    have : z.1 = uDecorHolePredTerm := by
      simpa [uDecorHolePredTerm, uTerm, xATerm, A, s, x, Ctx.plug] using hz
    simpa [this] using PredUTerm.decorHole
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    rcases plug_eq_xA_cases C' (t.op u) hleft with
      h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [xATerm] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uDecorLiftHolePredTerm := by
        simpa [uDecorLiftHolePredTerm, xADecorHolePredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.decorLiftHole
    ·
      rcases h1 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h2 with ⟨hC', hEq⟩
      subst hC'
      dsimp [A, s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uDecorLiftAPredTerm := by
        simpa [uDecorLiftAPredTerm, xADecorAPredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.decorLiftA
    ·
      rcases h3 with ⟨hC', hEq⟩
      subst hC'
      dsimp [s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uDecorLiftLeftSPredTerm := by
        simpa [uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.decorLiftLeftS
    ·
      rcases h4 with ⟨hC', hEq⟩
      subst hC'
      dsimp [s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uDecorLiftRightSPredTerm := by
        simpa [uDecorLiftRightSPredTerm, xADecorRightSPredTerm, xATerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.decorLiftRightS
    ·
      rcases h5 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h6 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h7 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h8 with ⟨_, hEq⟩
      cases hEq
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_s_cases C' (t.op u) hright with h0 | h1 | h2
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [s, x] at hEq
      injection hEq with ht hu
      subst t
      subst u
      have : z.1 = uDecorRightPredTerm := by
        simpa [uDecorRightPredTerm, xATerm, vTerm, A, s, x, Ctx.plug] using hz
      simpa [this] using PredUTerm.decorRight
    ·
      rcases h1 with ⟨_, hEq⟩
      cases hEq
    ·
      rcases h2 with ⟨_, hEq⟩
      cases hEq

private theorem c2c1_pred_to_nfU_isPred {z : NormalForm V} :
    NFC2C1StepCtx (α := V) z nfU → PredUTerm z.1 := by
  rintro ⟨C, x0, p, z0, hz, hu⟩
  have hu' : Ctx.plug C (((x0.op (p.op z0)).op z0)) = uTerm := by
    simpa [nfU] using hu.symm
  rcases plug_eq_uTerm_rhs_cases C (((x0.op (p.op z0)).op z0)) hu' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [uTerm, xATerm, A, s, x] at hEq
    injection hEq with hL hR
    subst z0
    injection hL with hx0 hp
    subst x0
    injection hp with hp1 hp2
    subst p
    have : z.1 = uHolePredTerm := by
      simpa [uHolePredTerm, uTerm, xATerm, A, s, x, Ctx.plug] using hz
    simpa [this] using PredUTerm.hole
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact False.elim (no_plug_c2c1_rhs_eq_xATerm C' x0 p z0 hleft)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact False.elim (no_plug_c2c1_rhs_eq_s C' x0 p z0 hright)
theorem NFStepR_to_nfU_isPred {z : NormalForm V} :
    NFStepR (α := V) R4 z nfU → PredUTerm z.1 := by
  intro h
  rcases h with ⟨tag, htag, hstep⟩
  have htag' :
      tag = RuleId.SqAbsorb ∨
      tag = RuleId.SqStable ∨
      tag = RuleId.Decor ∨
      tag = RuleId.C2C1 := by
    simpa [R4] using htag
  rcases htag' with rfl | rfl | rfl | rfl
  ·
    exact sqAbsorb_pred_to_nfU_isPred
      (z := z) (show NFSqStepCtx (α := V) z nfU from hstep)
  ·
    exact sqStable_pred_to_nfU_isPred
      (z := z) (show NFSqStableStepCtx (α := V) z nfU from hstep)
  ·
    exact decor_pred_to_nfU_isPred
      (z := z) (show NFDecorStepCtx (α := V) z nfU from hstep)
  ·
    exact c2c1_pred_to_nfU_isPred
      (z := z) (show NFC2C1StepCtx (α := V) z nfU from hstep)

theorem NFAdjR_at_nfU_isPred {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → PredUTerm z.1 := by
  intro h
  rcases h with h | h
  · exact False.elim (no_NFStepR_from_nfU (z := z) h)
  · exact NFStepR_to_nfU_isPred (z := z) h

private inductive AdjVTerm : Term V → Prop
  | sqHole : AdjVTerm vSqHolePredTerm
  | xA : AdjVTerm xATerm
  | decorHole : AdjVTerm vDecorHolePredTerm
  | decorRight : AdjVTerm vDecorRightPredTerm

theorem NFAdjR_at_nfV_isAdjVTerm {z : NormalForm V} :
    NFAdjR (α := V) R4 nfV z → AdjVTerm z.1 := by
  intro h
  rcases (NFAdjR_at_nfV_iff (z := z)).1 h with h | h | h | h
  · subst h
    exact AdjVTerm.sqHole
  · subst h
    exact AdjVTerm.xA
  · subst h
    exact AdjVTerm.decorHole
  · subst h
    exact AdjVTerm.decorRight

private inductive AdjXATerm : Term V → Prop
  | v : AdjXATerm vTerm
  | sqHole : AdjXATerm xASqHolePredTerm
  | sqA : AdjXATerm xASqAPredTerm
  | sqLeftS : AdjXATerm xASqLeftSPredTerm
  | sqRightS : AdjXATerm xASqRightSPredTerm
  | stable : AdjXATerm xAStablePredTerm
  | decorHole : AdjXATerm xADecorHolePredTerm
  | decorA : AdjXATerm xADecorAPredTerm
  | decorLeftS : AdjXATerm xADecorLeftSPredTerm
  | decorRightS : AdjXATerm xADecorRightSPredTerm

theorem NFAdjR_at_nfXA_isAdjXATerm {z : NormalForm V} :
  NFAdjR (α := V) R4 nfXA z → AdjXATerm z.1 := by
  intro h
  -- 1つ目だけ rfl にして、他は h_eq として等式を受け取る
  rcases NFAdjR_at_nfXA_term_cases (z := z) h with
    rfl | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq | h_eq
  -- z = nfV のケース (rfl によって置換済み)
  · exact AdjXATerm.v
  -- z.val = ... のケース (rw で z.1 を書き換えてから exact を適用)
  · rw [h_eq]; exact AdjXATerm.sqHole
  · rw [h_eq]; exact AdjXATerm.sqA
  · rw [h_eq]; exact AdjXATerm.sqLeftS
  · rw [h_eq]; exact AdjXATerm.sqRightS
  · rw [h_eq]; exact AdjXATerm.stable
  · rw [h_eq]; exact AdjXATerm.decorHole
  · rw [h_eq]; exact AdjXATerm.decorA
  · rw [h_eq]; exact AdjXATerm.decorLeftS
  · rw [h_eq]; exact AdjXATerm.decorRightS

private theorem PredUTerm_not_AdjVTerm {t : Term V} :
    PredUTerm t → ¬ AdjVTerm t := by
  intro hU hV
  cases hU <;> cases hV

private theorem PredUTerm_not_AdjXATerm {t : Term V} :
    PredUTerm t → ¬ AdjXATerm t := by
  intro hU hX
  cases hU <;> cases hX

theorem no_common_neighbor_nfU_nfV {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → ¬ NFAdjR (α := V) R4 nfV z := by
  intro hU hV
  exact PredUTerm_not_AdjVTerm
    (NFAdjR_at_nfU_isPred (z := z) hU)
    (NFAdjR_at_nfV_isAdjVTerm (z := z) hV)

theorem no_common_neighbor_nfU_nfXA {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → ¬ NFAdjR (α := V) R4 nfXA z := by
  intro hU hX
  exact PredUTerm_not_AdjXATerm
    (NFAdjR_at_nfU_isPred (z := z) hU)
    (NFAdjR_at_nfXA_isAdjXATerm (z := z) hX)

private theorem Ax_normal : Normal (α := V) (A.op x) := by
  apply (Normal_op_iff (α := V) A x).2
  refine ⟨A_normal_from_nfXA, x_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [A, s, x] at hw
    nomatch hw
  ·
    simp [IsC2pRoot, x]

private theorem xAStablePred_normal : Normal (α := V) xAStablePredTerm := by
  apply (Normal_op_iff (α := V) x (A.op x)).2
  refine ⟨x_normal_from_nfV, Ax_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    cases hw
  ·
    dsimp [IsC2pRoot, xAStablePredTerm, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem uStablePred_normal : Normal (α := V) uStablePredTerm := by
  apply (Normal_op_iff (α := V) xAStablePredTerm s).2
  refine ⟨xAStablePred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uStablePredTerm, xAStablePredTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uStablePredTerm, xAStablePredTerm, A, s, x]
    rintro ⟨w, hw⟩
    injection hw with hL hR
    cases hL

def nfUStablePred : NormalForm V := ⟨uStablePredTerm, uStablePred_normal⟩

theorem nfUStablePred_steps_to_nfU :
    NFStepR (α := V) R4 nfUStablePred nfU := by
  refine ⟨RuleId.SqStable, ?_, ?_⟩
  · simp [R4]
  · refine ⟨Ctx.left (Ctx.right x Ctx.hole) s, x, x, ?_, ?_⟩
    ·
      change uStablePredTerm
        = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s)
            ((((x.op x).op (x.op x)).op x))
      simp [Ctx.plug, uStablePredTerm, xAStablePredTerm, A, s, x]
    ·
      change uTerm
        = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s)
            ((x.op x).op (x.op x))
      simp [Ctx.plug, uTerm,  A, s, x]

def uStableAltTerm : Term V := (x.op (s.op x)).op s


def xAStableAltTerm : Term V := x.op (s.op x)


def nfXAStablePred : NormalForm V := ⟨xAStablePredTerm, xAStablePred_normal⟩


private theorem uHolePred_normal : Normal (α := V) uHolePredTerm := by
  apply (Normal_op_iff (α := V) uTerm A).2
  refine ⟨nfU.2, A_normal_from_nfXA, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uHolePredTerm, uTerm, xATerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uHolePredTerm, uTerm, xATerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

private theorem uDecorHolePred_normal : Normal (α := V) uDecorHolePredTerm := by
  apply (Normal_op_iff (α := V) uTerm (s.op A)).2
  refine ⟨nfU.2, sA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorHolePredTerm, uTerm, xATerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorHolePredTerm, uTerm, xATerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUHolePred : NormalForm V := ⟨uHolePredTerm, uHolePred_normal⟩
def nfUDecorHolePred : NormalForm V := ⟨uDecorHolePredTerm, uDecorHolePred_normal⟩



private theorem m_normal : Normal (α := V) mTerm := by
  apply (Normal_op_iff (α := V) vTerm (s.op vTerm)).2
  refine ⟨nfV.2, sv_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [mTerm, vTerm, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, mTerm, vTerm, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfM : NormalForm V := ⟨mTerm, m_normal⟩


private theorem uDecorRightPred_normal :
    Normal (α := V) uDecorRightPredTerm := by
  apply (Normal_op_iff (α := V) xATerm (s.op vTerm)).2
  refine ⟨nfXA.2, sv_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorRightPredTerm, xATerm, vTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorRightPredTerm, xATerm, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUDecorRightPred : NormalForm V := ⟨uDecorRightPredTerm, uDecorRightPred_normal⟩


private theorem xASqRightSPred_normal :
    Normal (α := V) xASqRightSPredTerm := by
  apply (Normal_op_iff (α := V) x (s.op A)).2
  refine ⟨x_normal_from_nfV, sA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    cases hw
  ·
    dsimp [IsC2pRoot, xASqRightSPredTerm, s, A, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem uSqLiftRightSPred_normal :
    Normal (α := V) uSqLiftRightSPredTerm := by
  apply (Normal_op_iff (α := V) xASqRightSPredTerm s).2
  refine ⟨xASqRightSPred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uSqLiftRightSPredTerm, xASqRightSPredTerm, s, A, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uSqLiftRightSPredTerm, xASqRightSPredTerm, s, A, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUSqLiftRightSPred : NormalForm V :=
  ⟨uSqLiftRightSPredTerm, uSqLiftRightSPred_normal⟩

theorem nfUSqLiftRightSPred_steps_to_nfU :
    NFStepR (α := V) R4 nfUSqLiftRightSPred nfU := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
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

def nfXASqRightPred : NormalForm V :=
  ⟨xASqRightSPredTerm, xASqRightSPred_normal⟩


private theorem ssv_normal :
    Normal (α := V) (s.op (s.op vTerm)) := by
  apply (Normal_op_iff (α := V) s (s.op vTerm)).2
  refine ⟨s_normal_from_nfV, sv_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [s, vTerm, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, s, vTerm, x]
    rintro ⟨w, hw⟩
    nomatch hw

theorem xADecorRightSPred_normal :
    Normal (α := V) xADecorRightSPredTerm := by
  apply (Normal_op_iff (α := V) x (s.op (s.op vTerm))).2
  refine ⟨x_normal_from_nfV, ssv_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    cases hw
  ·
    dsimp [IsC2pRoot, xADecorRightSPredTerm, vTerm, s, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem uDecorLiftRightSPred_normal :
    Normal (α := V) uDecorLiftRightSPredTerm := by
  apply (Normal_op_iff (α := V) xADecorRightSPredTerm s).2
  refine ⟨xADecorRightSPred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorLiftRightSPredTerm, xADecorRightSPredTerm, vTerm, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorLiftRightSPredTerm, xADecorRightSPredTerm, vTerm, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUDecorLiftRightSPred : NormalForm V :=
  ⟨uDecorLiftRightSPredTerm, uDecorLiftRightSPred_normal⟩

theorem nfUDecorLiftRightSPred_steps_to_nfU :
    NFStepR (α := V) R4 nfUDecorLiftRightSPred nfU := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s, x, x, ?_, ?_⟩
    ·
      change uDecorLiftRightSPredTerm
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s)
            ((x.op x).op (x.op (x.op x)))
      simp [Ctx.plug, uDecorLiftRightSPredTerm, xADecorRightSPredTerm,  s, x]
    ·
      change uTerm
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s Ctx.hole)) s)
            (x.op x)
      simp [Ctx.plug, uTerm,  A, s, x]

private theorem uSqLiftLeftSPred_not_normal :
    ¬ Normal (α := V) uSqLiftLeftSPredTerm := by
  intro hN
  have hL : Normal (α := V) xASqLeftSPredTerm :=
    ((Normal_op_iff (α := V) xASqLeftSPredTerm s).1 hN).1
  have hR : Normal (α := V) (A.op s) :=
    ((Normal_op_iff (α := V) x (A.op s)).1 hL).2.1
  have hnoC1 : ¬ IsC1Root (α := V) A s :=
    ((Normal_op_iff (α := V) A s).1 hR).2.2.1
  apply hnoC1
  refine ⟨s, ?_⟩
  dsimp [A, s, x]

private theorem uSqRightPred_not_normal :
    ¬ Normal (α := V) uSqRightPredTerm := by
  intro hN
  have hnoC1 : ¬ IsC1Root (α := V) xATerm A :=
    ((Normal_op_iff (α := V) xATerm A).1 hN).2.2.1
  apply hnoC1
  refine ⟨x, ?_⟩
  dsimp [uSqRightPredTerm, xATerm, A, s, x]

theorem AA_normal :
    Normal (α := V) (A.op A) := by
  apply (Normal_op_iff (α := V) A A).2
  refine ⟨A_normal_from_nfXA, A_normal_from_nfXA, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

private theorem xASqHolePred_normal :
    Normal (α := V) xASqHolePredTerm := by
  apply (Normal_op_iff (α := V) xATerm (A.op A)).2
  refine ⟨nfXA.2, AA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [xASqHolePredTerm, xATerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, xASqHolePredTerm, xATerm, A, s, x]
    rintro ⟨w, hw⟩
    injection hw with hL hR
    cases hL

theorem uSqLiftHolePred_normal :
    Normal (α := V) uSqLiftHolePredTerm := by
  apply (Normal_op_iff (α := V) xASqHolePredTerm s).2
  refine ⟨xASqHolePred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uSqLiftHolePredTerm, xASqHolePredTerm, xATerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uSqLiftHolePredTerm, xASqHolePredTerm, xATerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

theorem xASqAPred_normal :
    Normal (α := V) xASqAPredTerm := by
  apply (Normal_op_iff (α := V) x (A.op A)).2
  refine ⟨x_normal_from_nfV, AA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    cases hw
  ·
    dsimp [IsC2pRoot, xASqAPredTerm, A, s, x]
    rintro ⟨w, hw⟩
    cases hw

theorem uSqLiftAPred_normal :
    Normal (α := V) uSqLiftAPredTerm := by
  apply (Normal_op_iff (α := V) xASqAPredTerm s).2
  refine ⟨xASqAPred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uSqLiftAPredTerm, xASqAPredTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uSqLiftAPredTerm, xASqAPredTerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

theorem A_AA_normal :
    Normal (α := V) (A.op (A.op A)) := by
  apply (Normal_op_iff (α := V) A (A.op A)).2
  refine ⟨A_normal_from_nfXA, AA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

private theorem xADecorHolePred_normal :
    Normal (α := V) xADecorHolePredTerm := by
  apply (Normal_op_iff (α := V) xATerm (A.op (A.op A))).2
  refine ⟨nfXA.2, A_AA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [xADecorHolePredTerm, xATerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, xADecorHolePredTerm, xATerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

private theorem uDecorLiftHolePred_normal :
    Normal (α := V) uDecorLiftHolePredTerm := by
  apply (Normal_op_iff (α := V) xADecorHolePredTerm s).2
  refine ⟨xADecorHolePred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorLiftHolePredTerm, xADecorHolePredTerm, xATerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorLiftHolePredTerm, xADecorHolePredTerm, xATerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

private theorem AsA_normal :
    Normal (α := V) (A.op (s.op A)) := by
  apply (Normal_op_iff (α := V) A (s.op A)).2
  refine ⟨A_normal_from_nfXA, sA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

private theorem xADecorAPred_normal :
    Normal (α := V) xADecorAPredTerm := by
  apply (Normal_op_iff (α := V) x (A.op (s.op A))).2
  refine ⟨x_normal_from_nfV, AsA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    cases hw
  ·
    dsimp [IsC2pRoot, xADecorAPredTerm, A, s, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem uDecorLiftAPred_normal :
    Normal (α := V) uDecorLiftAPredTerm := by
  apply (Normal_op_iff (α := V) xADecorAPredTerm s).2
  refine ⟨xADecorAPred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorLiftAPredTerm, xADecorAPredTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorLiftAPredTerm, xADecorAPredTerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

private theorem svs_normal :
    Normal (α := V) ((s.op vTerm).op s) := by
  apply (Normal_op_iff (α := V) (s.op vTerm) s).2
  refine ⟨sv_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [vTerm, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, vTerm, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

theorem xADecorLeftSPred_normal :
    Normal (α := V) xADecorLeftSPredTerm := by
  have hsvs : Normal (α := V) (((s.op (x.op s))).op s) := by
    simpa [vTerm] using (svs_normal : Normal (α := V) ((s.op vTerm).op s))
  apply (Normal_op_iff (α := V) x (((s.op (x.op s))).op s)).2
  refine ⟨x_normal_from_nfV, hsvs, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    cases hw
  ·
    dsimp [IsC2pRoot, xADecorLeftSPredTerm, s, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem uDecorLiftLeftSPred_normal :
    Normal (α := V) uDecorLiftLeftSPredTerm := by
  apply (Normal_op_iff (α := V) xADecorLeftSPredTerm s).2
  refine ⟨xADecorLeftSPred_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, vTerm, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, vTerm, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

theorem NFStepR_to_nfU_actual_cases {z : NormalForm V} :
    NFStepR (α := V) R4 z nfU →
      z.1 = uHolePredTerm ∨
      z.1 = uSqLiftHolePredTerm ∨
      z.1 = uSqLiftAPredTerm ∨
      z.1 = uSqLiftRightSPredTerm ∨
      z.1 = uStablePredTerm ∨
      z.1 = uDecorHolePredTerm ∨
      z.1 = uDecorLiftHolePredTerm ∨
      z.1 = uDecorLiftAPredTerm ∨
      z.1 = uDecorLiftLeftSPredTerm ∨
      z.1 = uDecorLiftRightSPredTerm ∨
      z.1 = uDecorRightPredTerm := by
  rintro h
  rcases z with ⟨t, ht⟩
  have hPred : PredUTerm t := NFStepR_to_nfU_isPred (z := ⟨t, ht⟩) h
  cases hPred with
  | hole =>
      exact Or.inl rfl
  | sqLiftHole =>
      exact Or.inr (Or.inl rfl)
  | sqLiftA =>
      exact Or.inr (Or.inr (Or.inl rfl))
  | sqLiftLeftS =>
      exact False.elim <| uSqLiftLeftSPred_not_normal ht
  | sqLiftRightS =>
      exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | sqRight =>
      exact False.elim <| uSqRightPred_not_normal ht
  | stable =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | decorHole =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | decorLiftHole =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  | decorLiftA =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | decorLiftLeftS =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  | decorLiftRightS =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  | decorRight =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))

theorem NFAdjR_at_nfU_to_cases {z : NormalForm V} :
    NFStepR (α := V) R4 z nfU →
      z.1 = uHolePredTerm ∨
      z.1 = uSqLiftHolePredTerm ∨
      z.1 = uSqLiftAPredTerm ∨
      z.1 = uSqLiftRightSPredTerm ∨
      z.1 = uStablePredTerm ∨
      z.1 = uDecorHolePredTerm ∨
      z.1 = uDecorLiftHolePredTerm ∨
      z.1 = uDecorLiftAPredTerm ∨
      z.1 = uDecorLiftLeftSPredTerm ∨
      z.1 = uDecorLiftRightSPredTerm ∨
      z.1 = uDecorRightPredTerm := by
  intro h
  exact NFStepR_to_nfU_actual_cases (z := z) h

theorem NFAdjR_at_nfU_actual_cases {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z →
      z.1 = uHolePredTerm ∨
      z.1 = uSqLiftHolePredTerm ∨
      z.1 = uSqLiftAPredTerm ∨
      z.1 = uSqLiftRightSPredTerm ∨
      z.1 = uStablePredTerm ∨
      z.1 = uDecorHolePredTerm ∨
      z.1 = uDecorLiftHolePredTerm ∨
      z.1 = uDecorLiftAPredTerm ∨
      z.1 = uDecorLiftLeftSPredTerm ∨
      z.1 = uDecorLiftRightSPredTerm ∨
      z.1 = uDecorRightPredTerm := by
  intro hAdj
  rcases hAdj with hFrom | hTo
  ·
    exfalso
    exact no_NFStepR_from_nfU (z := z) hFrom
  ·
    exact NFStepR_to_nfU_actual_cases (z := z) hTo

theorem NFAdjR_at_nfU_not_AdjVTerm {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → ¬ AdjVTerm z.1 := by
  intro hU
  exact PredUTerm_not_AdjVTerm (NFAdjR_at_nfU_isPred (z := z) hU)

theorem NFAdjR_at_nfU_not_AdjXATerm {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → ¬ AdjXATerm z.1 := by
  intro hU
  exact PredUTerm_not_AdjXATerm (NFAdjR_at_nfU_isPred (z := z) hU)
--no_common_neighbor_nfU_nfV
--本質的に同じものはあるが論理の見通しを良くするため
theorem no_common_neighbor_nfU_nfV' {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → ¬ NFAdjR (α := V) R4 nfV z := by
  intro hU hV
  exact (NFAdjR_at_nfU_not_AdjVTerm (z := z) hU)
    (NFAdjR_at_nfV_isAdjVTerm (z := z) hV)
--no_common_neighbor_nfU_nfXA
--本質的に同じものはあるが論理の見通しを良くするため
theorem no_common_neighbor_nfU_nfXA' {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → ¬ NFAdjR (α := V) R4 nfXA z := by
  intro hU hX
  exact (NFAdjR_at_nfU_not_AdjXATerm (z := z) hU)
    (NFAdjR_at_nfXA_isAdjXATerm (z := z) hX)

def nfUSqLiftHolePred : NormalForm V :=
  ⟨uSqLiftHolePredTerm, uSqLiftHolePred_normal⟩

def nfUSqLiftAPred : NormalForm V :=
  ⟨uSqLiftAPredTerm, uSqLiftAPred_normal⟩

def nfUDecorLiftHolePred : NormalForm V :=
  ⟨uDecorLiftHolePredTerm, uDecorLiftHolePred_normal⟩

def nfUDecorLiftAPred : NormalForm V :=
  ⟨uDecorLiftAPredTerm, uDecorLiftAPred_normal⟩

def nfUDecorLiftLeftSPred : NormalForm V :=
  ⟨uDecorLiftLeftSPredTerm, uDecorLiftLeftSPred_normal⟩

theorem nfUSqLiftHolePred_steps_to_nfU :
    NFStepR (α := V) R4 nfUSqLiftHolePred nfU := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left Ctx.hole s, x, A, ?_, ?_⟩
    ·
      change uSqLiftHolePredTerm
        = Ctx.plug (Ctx.left Ctx.hole s) (((x.op A).op (A.op A)))
      simp [Ctx.plug, uSqLiftHolePredTerm, xASqHolePredTerm, xATerm,  A, s, x]
    ·
      change uTerm = Ctx.plug (Ctx.left Ctx.hole s) (x.op A)
      simp [Ctx.plug, uTerm, A, s, x]

theorem nfUSqLiftAPred_steps_to_nfU :
    NFStepR (α := V) R4 nfUSqLiftAPred nfU := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right x Ctx.hole) s, s, s, ?_, ?_⟩
    ·
      change uSqLiftAPredTerm
        = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s) (((s.op s).op (s.op s)))
      simp [Ctx.plug, uSqLiftAPredTerm, xASqAPredTerm,  A, s, x]
    ·
      change uTerm = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s) (s.op s)
      simp [Ctx.plug, uTerm,  A, s, x]

theorem nfUDecorLiftHolePred_steps_to_nfU :
    NFStepR (α := V) R4 nfUDecorLiftHolePred nfU := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left Ctx.hole s, x, A, ?_, ?_⟩
    ·
      change uDecorLiftHolePredTerm
        = Ctx.plug (Ctx.left Ctx.hole s) ((x.op A).op (A.op (A.op A)))
      simp [Ctx.plug, uDecorLiftHolePredTerm, xADecorHolePredTerm, xATerm,  A, s, x]
    ·
      change uTerm = Ctx.plug (Ctx.left Ctx.hole s) (x.op A)
      simp [Ctx.plug, uTerm,  A, s, x]

theorem nfUDecorLiftAPred_steps_to_nfU :
    NFStepR (α := V) R4 nfUDecorLiftAPred nfU := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right x Ctx.hole) s, s, s, ?_, ?_⟩
    ·
      change uDecorLiftAPredTerm
        = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s) (((s.op s).op (s.op (s.op s))))
      simp [Ctx.plug, uDecorLiftAPredTerm, xADecorAPredTerm,  A, s, x]
    ·
      change uTerm = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s) (s.op s)
      simp [Ctx.plug, uTerm, A, s, x]

theorem nfUDecorLiftLeftSPred_steps_to_nfU :
    NFStepR (α := V) R4 nfUDecorLiftLeftSPred nfU := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right x (Ctx.left Ctx.hole s)) s, x, x, ?_, ?_⟩
    ·
      change uDecorLiftLeftSPredTerm
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole s)) s)
            (((x.op x).op (x.op (x.op x))))
      simp [Ctx.plug, uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, s, x]
    ·
      change uTerm
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole s)) s) (x.op x)
      simp [Ctx.plug, uTerm,  A, s, x]

theorem plug_eq_sv_rhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = s.op vTerm) :
    (C = Ctx.hole ∧ r = s.op vTerm) ∨
    (∃ C', C = Ctx.left C' vTerm ∧ Ctx.plug C' r = s) ∨
    (∃ C', C = Ctx.right s C' ∧ Ctx.plug C' r = vTerm) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r0 =>
      dsimp [Ctx.plug, vTerm, s, x] at h
      injection h with hL hR
      subst hR
      exact Or.inr (Or.inl ⟨C, rfl, by simpa [s] using hL⟩)
  | right l C =>
      dsimp [Ctx.plug, vTerm, s, x] at h
      injection h with hL hR
      subst hL
      exact Or.inr (Or.inr ⟨C, rfl, by simpa [vTerm] using hR⟩)

theorem decor_rhs_eq_sv_forces_step_eq_s
    {t u : Term V}
    (hEq : (t.op u).op (u.op (u.op u)) = s.op vTerm) :
    t.op u = s := by
  dsimp [vTerm, s, x] at hEq
  injection hEq

theorem no_sqAbsorb_rhs_root_eq_sv
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ s.op vTerm := by
  intro hEq
  dsimp [vTerm, s, x] at hEq
  nomatch hEq

theorem no_sqStable_rhs_root_eq_sv
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ s.op vTerm := by
  intro hEq
  dsimp [vTerm, s, x] at hEq
  nomatch hEq

theorem nfXA_steps_to_nfV :
    NFStepR (α := V) R4 nfXA nfV := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.right x Ctx.hole, x, x, ?_, ?_⟩
    ·
      change xATerm = Ctx.plug (Ctx.right x Ctx.hole) (((x.op x).op (x.op x)))
      simp [Ctx.plug, xATerm, A, s, x]
    ·
      change vTerm = Ctx.plug (Ctx.right x Ctx.hole) (x.op x)
      simp [Ctx.plug, vTerm, s, x]

theorem plug_eq_uDecorRightPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uDecorRightPredTerm) :
    (C = Ctx.hole ∧ r = uDecorRightPredTerm) ∨
    (∃ C', C = Ctx.left C' (s.op vTerm) ∧ Ctx.plug C' r = xATerm) ∨
    (∃ C', C = Ctx.right xATerm C' ∧ Ctx.plug C' r = s.op vTerm) := by
  simpa [uDecorRightPredTerm] using plug_eq_op_cases C r xATerm (s.op vTerm) h

private theorem sqAbsorb_root_uDecorRightPred_forces_u_eq_s :
    RootMatchForces sqAbsorbPat uDecorRightPredTerm
      (fun σ => σ 1 = s) := by
  intro σ hEq
  dsimp [sqAbsorbPat, Pat.inst, uDecorRightPredTerm, xATerm, vTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem sqAbsorb_root_uDecorRightPred_refute_of_u_eq_s :
    ∀ σ, σ 1 = s → Pat.inst σ sqAbsorbPat ≠ uDecorRightPredTerm := by
  intro σ hus hEq
  dsimp [sqAbsorbPat, Pat.inst] at hEq
  rw [hus] at hEq
  dsimp [uDecorRightPredTerm, xATerm, vTerm, A, s, x] at hEq
  injection hEq with hL hR
  cases hR

def sqAbsorbRF_uDecorRightPred :
    SqAbsorbRightForcingWitness uDecorRightPredTerm where
  Φ := fun σ => σ 1 = s
  forces := sqAbsorb_root_uDecorRightPred_forces_u_eq_s
  refute := sqAbsorb_root_uDecorRightPred_refute_of_u_eq_s

private theorem no_sqStable_root_uDecorRightPred :
    SqStableGlobalNoRootWitness uDecorRightPredTerm := by
  intro σ hEq
  dsimp [sqStablePat, Pat.inst, uDecorRightPredTerm, xATerm, vTerm, A, s, x] at hEq
  nomatch hEq

private theorem decor_root_uDecorRightPred_forces_u_eq_s :
    RootMatchForces decorPat uDecorRightPredTerm
      (fun σ => σ 1 = s) := by
  intro σ hEq
  dsimp [decorPat, Pat.inst, uDecorRightPredTerm, xATerm, vTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem decor_root_uDecorRightPred_refute_of_u_eq_s :
    ∀ σ, σ 1 = s → Pat.inst σ decorPat ≠ uDecorRightPredTerm := by
  intro σ hus hEq
  dsimp [decorPat, Pat.inst] at hEq
  rw [hus] at hEq
  dsimp [uDecorRightPredTerm, xATerm, vTerm, A, s, x] at hEq
  injection hEq with hL hR
  cases hR

def decorRF_uDecorRightPred :
    DecorRightForcingWitness uDecorRightPredTerm where
  Φ := fun σ => σ 1 = s
  forces := decor_root_uDecorRightPred_forces_u_eq_s
  refute := decor_root_uDecorRightPred_refute_of_u_eq_s

private theorem no_c2c1_root_uDecorRightPred :
    C2C1GlobalNoRootWitness uDecorRightPredTerm := by
  intro σ hEq
  dsimp [c2c1Pat, Pat.inst, uDecorRightPredTerm, xATerm, vTerm, A, s, x] at hEq
  nomatch hEq

theorem no_sqAbsorb_root_eq_uDecorRightPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorRightPredTerm := by
  exact no_sqAbsorb_root_eq_of_rightForcing sqAbsorbRF_uDecorRightPred t u

theorem no_sqStable_root_eq_uDecorRightPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uDecorRightPredTerm := by
  exact no_sqStable_root_eq_of_globalNoRoot no_sqStable_root_uDecorRightPred t u

theorem no_decor_root_eq_uDecorRightPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uDecorRightPredTerm := by
  exact no_decor_root_eq_of_rightForcing decorRF_uDecorRightPred t u

theorem no_c2c1_root_eq_uDecorRightPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uDecorRightPredTerm := by
  exact no_c2c1_root_eq_of_globalNoRoot no_c2c1_root_uDecorRightPred x0 p z0

theorem no_c2c1_lhs_root_eq_sv
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ s.op vTerm := by
  intro hEq
  dsimp [s, vTerm, x] at hEq
  nomatch hEq


theorem nfUDecorRightPred_decor_to_nfU :
    NFDecorStepCtx (α := V) nfUDecorRightPred nfU := by
  refine ⟨Ctx.right xATerm Ctx.hole, x, x, ?_, ?_⟩
  ·
    change uDecorRightPredTerm
      = Ctx.plug (Ctx.right xATerm Ctx.hole) ((x.op x).op (x.op (x.op x)))
    simp [Ctx.plug, uDecorRightPredTerm, xATerm, vTerm, A, s, x]
  ·
    change uTerm = Ctx.plug (Ctx.right xATerm Ctx.hole) (x.op x)
    simp [Ctx.plug, uTerm, xATerm, A, s, x]
/- -/
theorem nfUDecorRightPred_steps_to_nfU :
    NFStepR (α := V) R4 nfUDecorRightPred nfU := by
  exact ⟨RuleId.Decor, by simp [R4], nfUDecorRightPred_decor_to_nfU⟩

theorem decor_succ_from_nfUDecorRightPred_eq_nfU {z : NormalForm V} :
    NFDecorStepCtx (α := V) nfUDecorRightPred z → z = nfU := by
  intro hstep
  rcases hstep with ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uDecorRightPredTerm := by
    simpa [nfUDecorRightPred] using hx.symm
  rcases plug_eq_uDecorRightPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_decor_root_eq_uDecorRightPred t u hEq)
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op (s.op vTerm) := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op (s.op vTerm)) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) (s.op vTerm)).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFDecorStepCtx (α := V) nfXA y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXA] using hleft.symm
    exact False.elim (no_decor_succ_from_nfXA (z := y) hy)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sv_rhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      have hstep' : t.op u = s :=
        decor_rhs_eq_sv_forces_step_eq_s hEq
      have hzVal : z.1 = uTerm := by
        rw [hstep'] at hz
        simpa [uTerm, xATerm, vTerm, s, x, Ctx.plug] using hz
      apply Subtype.ext
      simpa [nfU] using hzVal
    ·
      rcases hS with ⟨C'', hC'', hs⟩
      subst hC''
      exact False.elim (no_plug_decor_lhs_eq_s C'' t u hs)
    ·
      rcases hV with ⟨C'', hC'', hv⟩
      subst hC''
      exact False.elim (no_plug_decor_lhs_eq_vTerm C'' t u hv)

def ctxProfile_nfUDecorRightPred_decor : CtxProfile :=
  [(.right, .nfU)]

def ctxNFOfTag : CtxNFTag -> NormalForm V
  | .nfXA => nfXA
  | .nfXASqRightPred => nfXASqRightPred
  | .nfU => nfU
  | .nfUSqLiftRightPred => nfUSqLiftRightSPred
  | .nfUHolePred => nfUHolePred
  | .nfM => nfM

def ctxProfile_nfXASqAPred_sqAbsorb : CtxProfile :=
  [(.right, .nfXA), (.right, .nfXASqRightPred)]



theorem ctxProfileCert_nfUDecorRightPred_decor :
    CtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFDecorStepCtx (α := V) src z)
      nfUDecorRightPred
      ctxProfile_nfUDecorRightPred_decor := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [ctxProfile_nfUDecorRightPred_decor] at he
    rcases he with rfl
    exact nfUDecorRightPred_decor_to_nfU
  · intro z hz
    have hzEq : z = nfU := decor_succ_from_nfUDecorRightPred_eq_nfU (z := z) hz
    refine ⟨(.right, .nfU), by simp [ctxProfile_nfUDecorRightPred_decor], ?_⟩
    simpa [ctxNFOfTag] using hzEq

theorem no_sqStable_root_eq_uStablePred
    {t u : Term V}
    (hEq : (((t.op u).op (u.op u)).op u) = uStablePredTerm) :
    False := by
  dsimp [uStablePredTerm, xAStablePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem no_c2c1_root_eq_uStablePred
    {x0 p z0 : Term V}
    (hEq : (((x0.op (p.op z0)).op z0).op (p.op z0)) = uStablePredTerm) :
    False := by
  dsimp [uStablePredTerm, xAStablePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem sqAbsorb_root_eq_uHolePred_forces_step_eq_uTerm
    {t u : Term V}
    (hEq : ((t.op u).op (u.op u)) = uHolePredTerm) :
    t.op u = uTerm := by
  dsimp [uHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  injection hEq





theorem no_plug_sqAbsorb_lhs_eq_x
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C (((t.op u).op (u.op u))) ≠ x := by
  intro h
  rcases plug_eq_x_cases C (((t.op u).op (u.op u))) h with ⟨rfl, hEq⟩
  cases hEq

theorem no_plug_sqStable_lhs_eq_x
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((((t.op u).op (u.op u)).op u)) ≠ x := by
  intro h
  rcases plug_eq_x_cases C ((((t.op u).op (u.op u)).op u)) h with ⟨rfl, hEq⟩
  cases hEq

theorem no_plug_decor_lhs_eq_x
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((t.op u).op (u.op (u.op u))) ≠ x := by
  intro h
  rcases plug_eq_x_cases C ((t.op u).op (u.op (u.op u))) h with ⟨rfl, hEq⟩
  cases hEq

theorem no_plug_c2c1_lhs_eq_x
    (C : Ctx V) (x0 p z0 : Term V) :
    Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) ≠ x := by
  intro h
  rcases plug_eq_x_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) h with ⟨rfl, hEq⟩
  cases hEq

theorem plug_eq_xAStablePred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = xAStablePredTerm) :
    (C = Ctx.hole ∧ r = xAStablePredTerm) ∨
    (∃ C', C = Ctx.left C' (A.op x) ∧ Ctx.plug C' r = x) ∨
    (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = A.op x) := by
  simpa [xAStablePredTerm, x] using plug_eq_op_cases C r x (A.op x) h

theorem plug_eq_Ax_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = A.op x) :
    (C = Ctx.hole ∧ r = A.op x) ∨
    (∃ C', C = Ctx.left C' x ∧ Ctx.plug C' r = A) ∨
    (∃ C', C = Ctx.right A C' ∧ Ctx.plug C' r = x) := by
  simpa [A, x] using plug_eq_op_cases C r A x h

theorem no_sqAbsorb_root_x_left
    (q : Term V) :
    NoRootInstance sqAbsorbPat (x.op q) := by
  simpa [x] using
    (no_sqAbsorb_root_var_left_target (α := V) (a := (0 : V)) (q := q))

theorem no_sqStable_root_x_left
    (q : Term V) :
    NoRootInstance sqStablePat (x.op q) := by
  simpa [x] using
    (no_sqStable_root_var_left_target (α := V) (a := (0 : V)) (q := q))

theorem no_decor_root_x_left
    (q : Term V) :
    NoRootInstance decorPat (x.op q) := by
  simpa [x] using
    (no_decor_root_var_left_target (α := V) (a := (0 : V)) (q := q))

theorem no_c2c1_root_x_left
    (q : Term V) :
    NoRootInstance c2c1Pat (x.op q) := by
  simpa [x] using
    (no_c2c1_root_var_left_target (α := V) (a := (0 : V)) (q := q))

theorem no_plug_sqStable_lhs_eq_A
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((((t.op u).op (u.op u)).op u)) ≠ A := by
  intro h
  rcases plug_eq_A_cases C ((((t.op u).op (u.op u)).op u)) h with
    h0 | h1 | h2 | h3 | h4 | h5 | h6
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [A, s, x] at hEq
    nomatch hEq
  ·
    rcases h1 with ⟨_, hs⟩
    exact no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs)
  ·
    rcases h2 with ⟨_, hs⟩
    exact no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs)
  ·
    rcases h3 with ⟨_, hx⟩
    exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases h4 with ⟨_, hx⟩
    exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases h5 with ⟨_, hx⟩
    exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases h6 with ⟨_, hx⟩
    exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
theorem no_plug_decor_lhs_eq_A
    (C : Ctx V) (t u : Term V) :
    Ctx.plug C ((t.op u).op (u.op (u.op u))) ≠ A := by
  intro h
  rcases plug_eq_A_cases C ((t.op u).op (u.op (u.op u))) h with
    h0 | h1 | h2 | h3 | h4 | h5 | h6
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [A, s, x] at hEq
    nomatch hEq
  ·
    rcases h1 with ⟨_, hs⟩
    exact no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs)
  ·
    rcases h2 with ⟨_, hs⟩
    exact no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs)
  ·
    rcases h3 with ⟨_, hx⟩
    exact no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases h4 with ⟨_, hx⟩
    exact no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases h5 with ⟨_, hx⟩
    exact no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases h6 with ⟨_, hx⟩
    exact no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)

theorem no_plug_c2c1_lhs_eq_A
    (C : Ctx V) (x0 p z0 : Term V) :
    Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) ≠ A := by
  intro h
  rcases plug_eq_A_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) h with
    h0 | h1 | h2 | h3 | h4 | h5 | h6
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [A, s, x] at hEq
    nomatch hEq
  ·
    rcases h1 with ⟨_, hs⟩
    exact no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs)
  ·
    rcases h2 with ⟨_, hs⟩
    exact no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs)
  ·
    rcases h3 with ⟨_, hx⟩
    exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
  ·
    rcases h4 with ⟨_, hx⟩
    exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
  ·
    rcases h5 with ⟨_, hx⟩
    exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
  ·
    rcases h6 with ⟨_, hx⟩
    exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
theorem sqAbsorb_root_eq_A_forces_tu_eq_s
    {t u : Term V}
    (hEq : ((t.op u).op (u.op u)) = A) :
    t.op u = s := by
  dsimp [A, s, x] at hEq
  injection hEq

theorem plug_eq_sA_rhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = s.op A) :
    (C = Ctx.hole ∧ r = s.op A) ∨
    (∃ C', C = Ctx.left C' A ∧ Ctx.plug C' r = s) ∨
    (∃ C', C = Ctx.right s C' ∧ Ctx.plug C' r = A) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r0 =>
      dsimp [Ctx.plug, A, s, x] at h
      injection h with hL hR
      subst hR
      exact Or.inr (Or.inl ⟨C, rfl, by simpa [s] using hL⟩)
  | right l C =>
      dsimp [Ctx.plug, A, s, x] at h
      injection h with hL hR
      subst hL
      exact Or.inr (Or.inr ⟨C, rfl, by simpa [A] using hR⟩)

theorem no_sqAbsorb_root_eq_uDecorHolePred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorHolePredTerm := by
  intro hEq
  dsimp [uDecorHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem no_sqStable_root_eq_uDecorHolePred
    (t u : Term V) :
    ((((t.op u).op (u.op u)).op u)) ≠ uDecorHolePredTerm := by
  intro hEq
  dsimp [uDecorHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem decor_root_eq_uDecorHolePred_forces_step_eq_uTerm
    {t u : Term V}
    (hEq : ((t.op u).op (u.op (u.op u))) = uDecorHolePredTerm) :
    t.op u = uTerm := by
  dsimp [uDecorHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  injection hEq

theorem no_c2c1_root_eq_uDecorHolePred
    (x0 p z0 : Term V) :
    ((((x0.op (p.op z0)).op z0).op (p.op z0))) ≠ uDecorHolePredTerm := by
  intro hEq
  dsimp [uDecorHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem sqAbsorb_rhs_eq_sA_forces_tu_eq_s
    {t u : Term V}
    (hEq : ((t.op u).op (u.op u)) = s.op A) :
    t.op u = s := by
  dsimp [A, s, x] at hEq
  injection hEq

theorem no_sqStable_rhs_root_eq_sA
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ s.op A := by
  intro hEq
  dsimp [A, s, x] at hEq
  nomatch hEq

theorem no_decor_rhs_root_eq_sA
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ s.op A := by
  intro hEq
  dsimp [A, s, x] at hEq
  nomatch hEq

theorem no_c2c1_rhs_root_eq_sA
    (x0 p z0 : Term V) :
    ((x0.op (p.op z0)).op z0) ≠ s.op A := by
  intro hEq
  dsimp [A, s, x] at hEq
  nomatch hEq

theorem eq_nfU_of_left_val_sqRight {z : NormalForm V} {w : Term V}
    (hz' : z.1 = w.op s) (hw : w = xATerm) : z = nfU := by
  have hzVal : z.1 = uTerm := by
    rw [hw] at hz'
    simpa [uTerm, xATerm, s] using hz'
  apply Subtype.ext
  simpa [nfU] using hzVal

theorem eq_nfXA_of_right_val {z : NormalForm V} {w : Term V}
    (hz' : z.1 = x.op w)
    (hw : w = A) : z = nfXA := by
  apply Subtype.ext
  rw [hw] at hz'
  simpa [nfXA, xATerm] using hz'

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
