import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Core

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

/-!
Kernel-local implementation for the SA row pair
`nfXASqRightPred / nfUSqLiftRightSPred`.
This extracts the right-shell SA kernel from the former core monolith.
-/

theorem plug_eq_xASqRightPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = xASqRightSPredTerm) :
    (C = Ctx.hole ∧ r = xASqRightSPredTerm) ∨
    (∃ C', C = Ctx.left C' (s.op A) ∧ Ctx.plug C' r = x) ∨
    (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = s.op A) := by
  simpa [xASqRightSPredTerm] using plug_eq_op_cases C r x (s.op A) h

private theorem no_sqAbsorb_root_xASqRightPred :
    NoRootInstance sqAbsorbPat xASqRightSPredTerm := by
  simpa [xASqRightSPredTerm] using
    (no_sqAbsorb_root_x_left (q := s.op A))

private theorem no_sqStable_root_xASqRightPred :
    NoRootInstance sqStablePat xASqRightSPredTerm := by
  simpa [xASqRightSPredTerm] using
    (no_sqStable_root_x_left (q := s.op A))

private theorem no_decor_root_xASqRightPred :
    NoRootInstance decorPat xASqRightSPredTerm := by
  simpa [xASqRightSPredTerm] using
    (no_decor_root_x_left (q := s.op A))

private theorem no_c2c1_root_xASqRightPred :
    NoRootInstance c2c1Pat xASqRightSPredTerm := by
  simpa [xASqRightSPredTerm] using
    (no_c2c1_root_x_left (q := s.op A))

theorem no_sqAbsorb_root_eq_xASqRightPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xASqRightSPredTerm := by
  exact no_sqAbsorb_root_eq_of_no_instance no_sqAbsorb_root_xASqRightPred t u

theorem no_sqStable_root_eq_xASqRightPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xASqRightSPredTerm := by
  exact no_sqStable_root_eq_of_no_instance no_sqStable_root_xASqRightPred t u

theorem no_decor_root_eq_xASqRightPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xASqRightSPredTerm := by
  exact no_decor_root_eq_of_no_instance no_decor_root_xASqRightPred t u

theorem no_c2c1_root_eq_xASqRightPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xASqRightSPredTerm := by
  exact no_c2c1_root_eq_of_no_instance no_c2c1_root_xASqRightPred x0 p z0

private theorem no_sqAbsorb_rhs_root_eq_sA
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ s.op A := by
  intro hEq
  dsimp [A, s, x] at hEq
  nomatch hEq

theorem NFStepR_from_nfXASqRightPred_eq_nfXA {z : NormalForm V} :
    NFStepR (α := V) R4 nfXASqRightPred z → z = nfXA := by
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
    rcases (show NFSqStepCtx (α := V) nfXASqRightPred z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = xASqRightSPredTerm := by
      simpa [nfXASqRightPred] using hx.symm
    rcases plug_eq_xASqRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqAbsorb_root_eq_xASqRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_sqAbsorb_lhs_eq_x C' t u hleft)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sA_rhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hS | hA
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact False.elim (no_sqAbsorb_rhs_root_eq_sA t u hEq)
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact False.elim (no_plug_sqAbsorb_lhs_eq_s C'' t u hs)
      ·
        rcases hA with ⟨C'', hC'', hAeq⟩
        subst hC''
        rcases plug_eq_A_cases C'' (((t.op u).op (u.op u))) hAeq with
          hA0 | hA1 | hA2 | hA3 | hA4 | hA5 | hA6
        ·
          rcases hA0 with ⟨rfl, hEq⟩
          have htu : t.op u = s := sqAbsorb_root_eq_A_forces_tu_eq_s hEq
          apply Subtype.ext
          simpa [nfXA, xATerm, A, s, x, Ctx.plug, htu] using hz
        ·
          rcases hA1 with ⟨_, hs⟩
          exact False.elim (no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs))
        ·
          rcases hA2 with ⟨_, hs⟩
          exact False.elim (no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs))
        ·
          rcases hA3 with ⟨_, hx⟩
          exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
        ·
          rcases hA4 with ⟨_, hx⟩
          exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
        ·
          rcases hA5 with ⟨_, hx⟩
          exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
        ·
          rcases hA6 with ⟨_, hx⟩
          exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
  ·
    rcases (show NFSqStableStepCtx (α := V) nfXASqRightPred z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xASqRightSPredTerm := by
      simpa [nfXASqRightPred] using hx.symm
    rcases plug_eq_xASqRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqStable_root_eq_xASqRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_sqStable_lhs_eq_x C' t u hleft)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sA_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hS | hA
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact False.elim (no_sqStable_rhs_root_eq_sA t u hEq)
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact False.elim (no_plug_sqStable_lhs_eq_s C'' t u hs)
      ·
        rcases hA with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_sqStable_lhs_eq_A C'' t u hAeq)
  ·
    rcases (show NFDecorStepCtx (α := V) nfXASqRightPred z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xASqRightSPredTerm := by
      simpa [nfXASqRightPred] using hx.symm
    rcases plug_eq_xASqRightPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_decor_root_eq_xASqRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_decor_lhs_eq_x C' t u hleft)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sA_rhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hS | hA
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact False.elim (no_decor_rhs_root_eq_sA t u hEq)
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact False.elim (no_plug_decor_lhs_eq_s C'' t u hs)
      ·
        rcases hA with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_decor_lhs_eq_A C'' t u hAeq)
  ·
    rcases (show NFC2C1StepCtx (α := V) nfXASqRightPred z from hstep) with ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xASqRightSPredTerm := by
      simpa [nfXASqRightPred] using hx.symm
    rcases plug_eq_xASqRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_c2c1_root_eq_xASqRightPred x0 p z0 hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sA_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hright with h0 | hS | hA
      ·
        rcases h0 with ⟨rfl, hEq⟩
        dsimp [s, A, x] at hEq
        injection hEq with hL hR
        cases hL
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact False.elim (no_plug_c2c1_lhs_eq_s C'' x0 p z0 hs)
      ·
        rcases hA with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_c2c1_lhs_eq_A C'' x0 p z0 hAeq)

theorem nfXASqRightPred_steps_to_nfXA :
    NFStepR (α := V) R4 nfXASqRightPred nfXA := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
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

theorem sqAbsorb_succ_from_nfXASqRightPred_eq_nfXA {z : NormalForm V} :
    NFSqStepCtx (α := V) nfXASqRightPred z → z = nfXA := by
  intro hz
  exact NFStepR_from_nfXASqRightPred_eq_nfXA
    (z := z) ⟨RuleId.SqAbsorb, by simp [R4], hz⟩

theorem no_sqStable_succ_from_nfXASqRightPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfXASqRightPred z := by
  intro hstep
  rcases hstep with ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xASqRightSPredTerm := by
    simpa [nfXASqRightPred] using hx.symm
  rcases plug_eq_xASqRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_xASqRightPred t u hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_sqStable_lhs_eq_x C' t u hleft
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sA_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hS | hA
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_sqStable_rhs_root_eq_sA t u hEq
    ·
      rcases hS with ⟨C'', hC'', hs⟩
      subst hC''
      exact no_plug_sqStable_lhs_eq_s C'' t u hs
    ·
      rcases hA with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_sqStable_lhs_eq_A C'' t u hAeq

theorem no_decor_succ_from_nfXASqRightPred {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfXASqRightPred z := by
  intro hstep
  rcases hstep with ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xASqRightSPredTerm := by
    simpa [nfXASqRightPred] using hx.symm
  rcases plug_eq_xASqRightPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_decor_root_eq_xASqRightPred t u hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_decor_lhs_eq_x C' t u hleft
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sA_rhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hS | hA
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_decor_rhs_root_eq_sA t u hEq
    ·
      rcases hS with ⟨C'', hC'', hs⟩
      subst hC''
      exact no_plug_decor_lhs_eq_s C'' t u hs
    ·
      rcases hA with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_decor_lhs_eq_A C'' t u hAeq

theorem no_c2c1_succ_from_nfXASqRightPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfXASqRightPred z := by
  intro hstep
  rcases hstep with ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xASqRightSPredTerm := by
    simpa [nfXASqRightPred] using hx.symm
  rcases plug_eq_xASqRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_xASqRightPred x0 p z0 hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sA_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hright with h0 | hS | hA
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [s, A, x] at hEq
      injection hEq with hL hR
      cases hL
    ·
      rcases hS with ⟨C'', hC'', hs⟩
      subst hC''
      exact no_plug_c2c1_lhs_eq_s C'' x0 p z0 hs
    ·
      rcases hA with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_c2c1_lhs_eq_A C'' x0 p z0 hAeq

theorem plug_eq_uSqLiftRightPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uSqLiftRightSPredTerm) :
    (C = Ctx.hole ∧ r = uSqLiftRightSPredTerm) ∨
    (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xASqRightSPredTerm) ∨
    (∃ C', C = Ctx.right xASqRightSPredTerm C' ∧ Ctx.plug C' r = s) := by
  simpa [uSqLiftRightSPredTerm] using plug_eq_op_cases C r xASqRightSPredTerm s h



private theorem eq_nfU_of_sqAbsorb_left_case_from_xASqRight {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' (((t.op u).op (u.op u))) = xASqRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFSqStepCtx (α := V) nfXASqRightPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXASqRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXASqRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_sqStable_left_case_from_xASqRight {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((((t.op u).op (u.op u)).op u)) = xASqRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
  have hy : NFSqStableStepCtx (α := V) nfXASqRightPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXASqRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXASqRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqStable, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_decor_left_case_from_xASqRight {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((t.op u).op (u.op (u.op u))) = xASqRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFDecorStepCtx (α := V) nfXASqRightPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXASqRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXASqRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.Decor, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_c2c1_left_case_from_xASqRight {z : NormalForm V}
    {C' : Ctx V} {x0 p z0 : Term V}
    (hL : Ctx.plug C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xASqRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
  have hy : NFC2C1StepCtx (α := V) nfXASqRightPred y := by
    refine ⟨C', x0, p, z0, ?_, rfl⟩
    simpa [nfXASqRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXASqRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.C2C1, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

--
private theorem sqAbsorb_root_uSqLiftRightPred_forces_u_eq_x :
    RootMatchForces sqAbsorbPat uSqLiftRightSPredTerm
      (fun σ => σ 1 = x) := by
  intro σ hEq
  dsimp [sqAbsorbPat, Pat.inst, uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem sqAbsorb_root_uSqLiftRightPred_refute_of_u_eq_x :
    ∀ σ, σ 1 = x → Pat.inst σ sqAbsorbPat ≠ uSqLiftRightSPredTerm := by
  intro σ hux hEq
  dsimp [sqAbsorbPat, Pat.inst] at hEq
  rw [hux] at hEq
  dsimp [uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hL with ht hu
  cases hu

def sqAbsorbRF_uSqLiftRightPred :
    SqAbsorbRightForcingWitness uSqLiftRightSPredTerm where
  Φ := fun σ => σ 1 = x
  forces := sqAbsorb_root_uSqLiftRightPred_forces_u_eq_x
  refute := sqAbsorb_root_uSqLiftRightPred_refute_of_u_eq_x

private theorem no_sqStable_root_uSqLiftRightPred :
    SqStableGlobalNoRootWitness uSqLiftRightSPredTerm := by
  intro σ hEq
  dsimp [sqStablePat, Pat.inst, uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x] at hEq
  nomatch hEq

private theorem decor_root_uSqLiftRightPred_forces_u_eq_x :
    RootMatchForces decorPat uSqLiftRightSPredTerm
      (fun σ => σ 1 = x) := by
  intro σ hEq
  dsimp [decorPat, Pat.inst, uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem decor_root_uSqLiftRightPred_refute_of_u_eq_x :
    ∀ σ, σ 1 = x → Pat.inst σ decorPat ≠ uSqLiftRightSPredTerm := by
  intro σ hux hEq
  dsimp [decorPat, Pat.inst] at hEq
  rw [hux] at hEq
  dsimp [uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  cases hR

def decorRF_uSqLiftRightPred :
    DecorRightForcingWitness uSqLiftRightSPredTerm where
  Φ := fun σ => σ 1 = x
  forces := decor_root_uSqLiftRightPred_forces_u_eq_x
  refute := decor_root_uSqLiftRightPred_refute_of_u_eq_x

private theorem no_c2c1_root_uSqLiftRightPred :
    C2C1GlobalNoRootWitness uSqLiftRightSPredTerm := by
  intro σ hEq
  dsimp [c2c1Pat, Pat.inst, uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x] at hEq
  nomatch hEq
--

theorem no_sqAbsorb_root_eq_uSqLiftRightPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uSqLiftRightSPredTerm := by
  exact no_sqAbsorb_root_eq_of_rightForcing sqAbsorbRF_uSqLiftRightPred t u

theorem no_sqStable_root_eq_uSqLiftRightPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uSqLiftRightSPredTerm := by
  exact no_sqStable_root_eq_of_globalNoRoot no_sqStable_root_uSqLiftRightPred t u

theorem no_decor_root_eq_uSqLiftRightPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uSqLiftRightSPredTerm := by
  exact no_decor_root_eq_of_rightForcing decorRF_uSqLiftRightPred t u

theorem no_c2c1_root_eq_uSqLiftRightPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uSqLiftRightSPredTerm := by
  exact no_c2c1_root_eq_of_globalNoRoot no_c2c1_root_uSqLiftRightPred x0 p z0
theorem NFStepR_from_nfUSqLiftRightSPred_eq_nfU {z : NormalForm V} :
    NFStepR (α := V) R4 nfUSqLiftRightSPred z → z = nfU := by
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
    rcases (show NFSqStepCtx (α := V) nfUSqLiftRightSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uSqLiftRightSPredTerm := by
      simpa [nfUSqLiftRightSPred] using hx.symm
    rcases plug_eq_uSqLiftRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqAbsorb_root_eq_uSqLiftRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_sqAbsorb_left_case_from_xASqRight hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' (((t.op u).op (u.op u))) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim (no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs))
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
  ·
    rcases (show NFSqStableStepCtx (α := V) nfUSqLiftRightSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uSqLiftRightSPredTerm := by
      simpa [nfUSqLiftRightSPred] using hx.symm
    rcases plug_eq_uSqLiftRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqStable_root_eq_uSqLiftRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_sqStable_left_case_from_xASqRight hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' ((((t.op u).op (u.op u)).op u)) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim (no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs))
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
  ·
    rcases (show NFDecorStepCtx (α := V) nfUSqLiftRightSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uSqLiftRightSPredTerm := by
      simpa [nfUSqLiftRightSPred] using hx.symm
    rcases plug_eq_uSqLiftRightPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_decor_root_eq_uSqLiftRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_decor_left_case_from_xASqRight hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' ((t.op u).op (u.op (u.op u))) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim (no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs))
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
  ·
    rcases (show NFC2C1StepCtx (α := V) nfUSqLiftRightSPred z from hstep) with
      ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uSqLiftRightSPredTerm := by
      simpa [nfUSqLiftRightSPred] using hx.symm
    rcases plug_eq_uSqLiftRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_c2c1_root_eq_uSqLiftRightPred x0 p z0 hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_c2c1_left_case_from_xASqRight hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim (no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs))
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))


theorem sqAbsorb_succ_from_nfUSqLiftRightSPred_eq_nfU {z : NormalForm V} :
    NFSqStepCtx (α := V) nfUSqLiftRightSPred z → z = nfU := by
  intro hz
  exact NFStepR_from_nfUSqLiftRightSPred_eq_nfU
    (z := z) ⟨RuleId.SqAbsorb, by simp [R4], hz⟩

theorem no_sqStable_succ_from_nfUSqLiftRightSPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfUSqLiftRightSPred z := by
  intro hstep
  rcases hstep with ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uSqLiftRightSPredTerm := by
    simpa [nfUSqLiftRightSPred] using hx.symm
  rcases plug_eq_uSqLiftRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uSqLiftRightPred t u hEq
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
    have hy : NFSqStableStepCtx (α := V) nfXASqRightPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXASqRightPred] using hL.symm
    exact no_sqStable_succ_from_nfXASqRightPred hy
  ·
    rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' ((((t.op u).op (u.op u)).op u)) hS with h0 | h1 | h2
    ·
      rcases h0 with ⟨rfl, hs⟩
      exact no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs)
    ·
      rcases h1 with ⟨_, hx⟩
      exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
    ·
      rcases h2 with ⟨_, hx⟩
      exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)

theorem no_decor_succ_from_nfUSqLiftRightSPred {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfUSqLiftRightSPred z := by
  intro hstep
  rcases hstep with ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uSqLiftRightSPredTerm := by
    simpa [nfUSqLiftRightSPred] using hx.symm
  rcases plug_eq_uSqLiftRightPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_decor_root_eq_uSqLiftRightPred t u hEq
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFDecorStepCtx (α := V) nfXASqRightPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXASqRightPred] using hL.symm
    exact no_decor_succ_from_nfXASqRightPred hy
  ·
    rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' ((t.op u).op (u.op (u.op u))) hS with h0 | h1 | h2
    ·
      rcases h0 with ⟨rfl, hs⟩
      exact no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs)
    ·
      rcases h1 with ⟨_, hx⟩
      exact no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)
    ·
      rcases h2 with ⟨_, hx⟩
      exact no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)

theorem no_c2c1_succ_from_nfUSqLiftRightSPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfUSqLiftRightSPred z := by
  intro hstep
  rcases hstep with ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uSqLiftRightSPredTerm := by
    simpa [nfUSqLiftRightSPred] using hx.symm
  rcases plug_eq_uSqLiftRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_uSqLiftRightPred x0 p z0 hEq
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
    have hy : NFC2C1StepCtx (α := V) nfXASqRightPred y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfXASqRightPred] using hL.symm
    exact no_c2c1_succ_from_nfXASqRightPred hy
  ·
    rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hS with h0 | h1 | h2
    ·
      rcases h0 with ⟨rfl, hs⟩
      exact no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs)
    ·
      rcases h1 with ⟨_, hx⟩
      exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
    ·
      rcases h2 with ⟨_, hx⟩
      exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
