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

section KernelStableHoleBridge

theorem sx_not_normal :
    ¬ Normal (α := V) (s.op x) := by
  intro hN
  have hnoC1 : ¬ IsC1Root (α := V) s x :=
    ((Normal_op_iff (α := V) s x).1 hN).2.2.1
  apply hnoC1
  refine ⟨x, ?_⟩
  dsimp [s, x]

theorem x_sx_not_normal :
    ¬ Normal (α := V) (x.op (s.op x)) := by
  intro hN
  have hR : Normal (α := V) (s.op x) :=
    ((Normal_op_iff (α := V) x (s.op x)).1 hN).2.1
  exact sx_not_normal hR

theorem uStableAlt_not_normal :
    ¬ Normal (α := V) uStableAltTerm := by
  intro hN
  have hL : Normal (α := V) (x.op (s.op x)) :=
    ((Normal_op_iff (α := V) (x.op (s.op x)) s).1 hN).1
  exact x_sx_not_normal hL

theorem xAStableAlt_not_normal :
    ¬ Normal (α := V) xAStableAltTerm := by
  simpa [xAStableAltTerm] using x_sx_not_normal

theorem no_sqAbsorb_root_xAStablePred :
    NoRootInstance sqAbsorbPat xAStablePredTerm := by
  simpa [xAStablePredTerm] using
    (no_sqAbsorb_root_x_left (q := A.op x))

theorem no_sqStable_root_xAStablePred :
    NoRootInstance sqStablePat xAStablePredTerm := by
  simpa [xAStablePredTerm] using
    (no_sqStable_root_x_left (q := A.op x))

theorem no_decor_root_xAStablePred :
    NoRootInstance decorPat xAStablePredTerm := by
  simpa [xAStablePredTerm] using
    (no_decor_root_x_left (q := A.op x))

theorem no_c2c1_root_xAStablePred :
    NoRootInstance c2c1Pat xAStablePredTerm := by
  simpa [xAStablePredTerm] using
    (no_c2c1_root_x_left (q := A.op x))

theorem no_sqAbsorb_root_eq_xAStablePred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xAStablePredTerm := by
  exact no_sqAbsorb_root_eq_of_no_instance no_sqAbsorb_root_xAStablePred t u

theorem no_sqStable_root_eq_xAStablePred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xAStablePredTerm := by
  exact no_sqStable_root_eq_of_no_instance no_sqStable_root_xAStablePred t u

theorem no_decor_root_eq_xAStablePred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xAStablePredTerm := by
  exact no_decor_root_eq_of_no_instance no_decor_root_xAStablePred t u

theorem no_c2c1_root_eq_xAStablePred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xAStablePredTerm := by
  exact no_c2c1_root_eq_of_no_instance no_c2c1_root_xAStablePred x0 p z0


theorem sqAbsorb_succ_from_nfXAStablePred_alt {z : NormalForm V} :
    NFSqStepCtx (α := V) nfXAStablePred z → z.1 = xAStableAltTerm := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = xAStablePredTerm := by
    simpa [nfXAStablePred] using hx.symm
  rcases plug_eq_xAStablePred_lhs_cases C (((t.op u).op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_sqAbsorb_root_eq_xAStablePred t u hEq)
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact False.elim (no_plug_sqAbsorb_lhs_eq_x C' t u hleft)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_Ax_lhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hA | hX
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [A, s, x] at hEq
      injection hEq with hL hR
      cases hR
    ·
      rcases hA with ⟨C'', rfl, hAeq⟩
      rcases plug_eq_A_cases C'' (((t.op u).op (u.op u))) hAeq with
        hA0 | hA1 | hA2 | hA3 | hA4 | hA5 | hA6
      ·
        rcases hA0 with ⟨rfl, hEq⟩
        dsimp [A, s, x] at hEq
        injection hEq with ht hu
        injection ht with ht1 ht2
        cases ht1
        cases ht2
        simpa [xAStableAltTerm, x, s, Ctx.plug] using hz
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
      rcases hX with ⟨C'', rfl, hxeq⟩
      exact False.elim (no_plug_sqAbsorb_lhs_eq_x C'' t u hxeq)

theorem sqStable_succ_from_nfXAStablePred_eq_nfXA {z : NormalForm V} :
    NFSqStableStepCtx (α := V) nfXAStablePred z → z = nfXA := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xAStablePredTerm := by
    simpa [nfXAStablePred] using hx.symm
  rcases plug_eq_xAStablePred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_sqStable_root_eq_xAStablePred t u hEq)
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact False.elim (no_plug_sqStable_lhs_eq_x C' t u hleft)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_Ax_lhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hA | hX
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [A, s, x] at hEq
      injection hEq with hL hR
      injection hL with ht hu
      cases ht
      cases hu
      cases hR
      apply Subtype.ext
      simpa [nfXA, xATerm, A, s, x, Ctx.plug] using hz
    ·
      rcases hA with ⟨C'', rfl, hAeq⟩
      rcases plug_eq_A_cases C'' ((((t.op u).op (u.op u)).op u)) hAeq with
        hA0 | hA1 | hA2 | hA3 | hA4 | hA5 | hA6
      ·
        rcases hA0 with ⟨rfl, hEq⟩
        dsimp [A, s, x] at hEq
        injection hEq with hL hR
        subst hR
        injection hL with hLs hRs
        injection hLs
      ·
        rcases hA1 with ⟨_, hs⟩
        exact False.elim (no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs))
      ·
        rcases hA2 with ⟨_, hs⟩
        exact False.elim (no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs))
      ·
        rcases hA3 with ⟨_, hx⟩
        exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases hA4 with ⟨_, hx⟩
        exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases hA5 with ⟨_, hx⟩
        exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases hA6 with ⟨_, hx⟩
        exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
    ·
      rcases hX with ⟨C'', rfl, hxeq⟩
      exact False.elim (no_plug_sqStable_lhs_eq_x C'' t u hxeq)

theorem no_decor_succ_from_nfXAStablePred {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfXAStablePred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xAStablePredTerm := by
    simpa [nfXAStablePred] using hx.symm
  rcases plug_eq_xAStablePred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_decor_root_eq_xAStablePred t u hEq)
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact False.elim (no_plug_decor_lhs_eq_x C' t u hleft)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_Ax_lhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hA | hX
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [A, s, x] at hEq
      injection hEq with hL hR
      cases hR
    ·
      rcases hA with ⟨C'', rfl, hAeq⟩
      rcases plug_eq_A_cases C'' ((t.op u).op (u.op (u.op u))) hAeq with
        hA0 | hA1 | hA2 | hA3 | hA4 | hA5 | hA6
      ·
        rcases hA0 with ⟨rfl, hEq⟩
        dsimp [A, s, x] at hEq
        injection hEq with hL hR
        cases hR
      ·
        rcases hA1 with ⟨_, hs⟩
        exact False.elim (no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs))
      ·
        rcases hA2 with ⟨_, hs⟩
        exact False.elim (no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs))
      ·
        rcases hA3 with ⟨_, hx⟩
        exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases hA4 with ⟨_, hx⟩
        exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases hA5 with ⟨_, hx⟩
        exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
      ·
        rcases hA6 with ⟨_, hx⟩
        exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
    ·
      rcases hX with ⟨C'', rfl, hxeq⟩
      exact False.elim (no_plug_decor_lhs_eq_x C'' t u hxeq)

theorem no_c2c1_succ_from_nfXAStablePred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfXAStablePred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xAStablePredTerm := by
    simpa [nfXAStablePred] using hx.symm
  rcases plug_eq_xAStablePred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_c2c1_root_eq_xAStablePred x0 p z0 hEq)
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact False.elim (no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_Ax_lhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hright with h0 | hA | hX
    ·
      rcases h0 with ⟨rfl, hEq⟩
      dsimp [A, s, x] at hEq
      injection hEq with hL hR
      cases hR
    ·
      rcases hA with ⟨C'', rfl, hAeq⟩
      rcases plug_eq_A_cases C'' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hAeq with
        hA0 | hA1 | hA2 | hA3 | hA4 | hA5 | hA6
      ·
        rcases hA0 with ⟨rfl, hEq⟩
        dsimp [A, s, x] at hEq
        injection hEq with hL hR
        injection hR with hp hz0
        subst hp
        subst hz0
        injection hL with hLs hRs
        injection hLs
      ·
        rcases hA1 with ⟨_, hs⟩
        exact False.elim (no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs))
      ·
        rcases hA2 with ⟨_, hs⟩
        exact False.elim (no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs))
      ·
        rcases hA3 with ⟨_, hx⟩
        exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))
      ·
        rcases hA4 with ⟨_, hx⟩
        exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))
      ·
        rcases hA5 with ⟨_, hx⟩
        exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))
      ·
        rcases hA6 with ⟨_, hx⟩
        exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))
    ·
      rcases hX with ⟨C'', rfl, hxeq⟩
      exact False.elim (no_plug_c2c1_lhs_eq_x C'' x0 p z0 hxeq)

theorem NFStepR_from_nfXAStablePred_eq_nfXA {z : NormalForm V} :
    NFStepR (α := V) R4 nfXAStablePred z → z = nfXA := by
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
    have hzAlt : z.1 = xAStableAltTerm :=
      sqAbsorb_succ_from_nfXAStablePred_alt
        (z := z) (show NFSqStepCtx (α := V) nfXAStablePred z from hstep)
    have : Normal (α := V) xAStableAltTerm := by
      simpa [hzAlt] using z.2
    exact False.elim (xAStableAlt_not_normal this)
  ·
    exact sqStable_succ_from_nfXAStablePred_eq_nfXA
      (z := z) (show NFSqStableStepCtx (α := V) nfXAStablePred z from hstep)
  ·
    exact False.elim <|
      no_decor_succ_from_nfXAStablePred
        (z := z) (show NFDecorStepCtx (α := V) nfXAStablePred z from hstep)
  ·
    exact False.elim <|
      no_c2c1_succ_from_nfXAStablePred
        (z := z) (show NFC2C1StepCtx (α := V) nfXAStablePred z from hstep)

theorem plug_eq_uStablePred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uStablePredTerm) :
    (C = Ctx.hole ∧ r = uStablePredTerm) ∨
    (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xAStablePredTerm) ∨
    (∃ C', C = Ctx.right xAStablePredTerm C' ∧ Ctx.plug C' r = s) := by
  simpa [uStablePredTerm] using plug_eq_op_cases C r xAStablePredTerm s h

private theorem eq_nfU_of_left_val {z : NormalForm V} {w : Term V}
    (hz' : z.1 = w.op s) (hw : w = xATerm) : z = nfU := by
  have hzVal : z.1 = uTerm := by
    rw [hw] at hz'
    simpa [uTerm, xATerm, s] using hz'
  apply Subtype.ext
  simpa [nfU] using hzVal

private theorem eq_nfU_of_sqAbsorb_left_case {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' (((t.op u).op (u.op u))) = xAStablePredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFSqStepCtx (α := V) nfXAStablePred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXAStablePred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXAStablePred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val hz' hyVal

private theorem eq_nfU_of_sqStable_left_case {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((((t.op u).op (u.op u)).op u)) = xAStablePredTerm)
    (hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
  have hy : NFSqStableStepCtx (α := V) nfXAStablePred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXAStablePred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXAStablePred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqStable, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val hz' hyVal

private theorem eq_nfU_of_decor_left_case {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((t.op u).op (u.op (u.op u))) = xAStablePredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFDecorStepCtx (α := V) nfXAStablePred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXAStablePred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXAStablePred_eq_nfXA
      (z := y) (by exact ⟨RuleId.Decor, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val hz' hyVal

private theorem eq_nfU_of_c2c1_left_case {z : NormalForm V}
    {C' : Ctx V} {x0 p z0 : Term V}
    (hL : Ctx.plug C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xAStablePredTerm)
    (hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
  have hy : NFC2C1StepCtx (α := V) nfXAStablePred y := by
    refine ⟨C', x0, p, z0, ?_, rfl⟩
    simpa [nfXAStablePred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXAStablePred_eq_nfXA
      (z := y) (by exact ⟨RuleId.C2C1, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val hz' hyVal

theorem no_sqAbsorb_root_eq_uStablePred
    {t u : Term V}
    (hEq : ((t.op u).op (u.op u)) = uStablePredTerm) :
    False := by
  dsimp [uStablePredTerm, xAStablePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem sqAbsorb_step_from_nfUStablePred_eq_nfU {z : NormalForm V} :
    NFSqStepCtx (α := V) nfUStablePred z → z = nfU := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uStablePredTerm := by
    simpa [nfUStablePred] using hx.symm
  rcases plug_eq_uStablePred_lhs_cases C (((t.op u).op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_sqAbsorb_root_eq_uStablePred hEq)
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    exact eq_nfU_of_sqAbsorb_left_case hL hz'
  ·
    rcases hR with ⟨C', hC, hS⟩
    subst hC
    exact False.elim (no_plug_sqAbsorb_lhs_eq_s C' t u hS)

theorem sqStable_step_from_nfUStablePred_eq_nfU {z : NormalForm V} :
    NFSqStableStepCtx (α := V) nfUStablePred z → z = nfU := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uStablePredTerm := by
    simpa [nfUStablePred] using hx.symm
  rcases plug_eq_uStablePred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [uStablePredTerm, xAStablePredTerm, A, s, x] at hEq
    injection hEq with hL hR
    cases hL
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
      simpa [Ctx.plug] using hz
    exact eq_nfU_of_sqStable_left_case hL hz'
  ·
    rcases hR with ⟨C', hC, hS⟩
    subst hC
    exact False.elim (no_plug_sqStable_lhs_eq_s C' t u hS)

theorem no_decor_root_eq_uStablePred
    {t u : Term V}
    (hEq : ((t.op u).op (u.op (u.op u))) = uStablePredTerm) :
    False := by
  dsimp [uStablePredTerm, xAStablePredTerm, uTerm, xATerm, A, s, x] at hEq
  injection hEq with hL hR
  cases hR

theorem decor_step_from_nfUStablePred_eq_nfU {z : NormalForm V} :
    NFDecorStepCtx (α := V) nfUStablePred z → z = nfU := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uStablePredTerm := by
    simpa [nfUStablePred] using hx.symm
  rcases plug_eq_uStablePred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_decor_root_eq_uStablePred hEq)
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    exact eq_nfU_of_decor_left_case hL hz'
  ·
    rcases hR with ⟨C', hC, hS⟩
    subst hC
    exact False.elim (no_plug_decor_lhs_eq_s C' t u hS)

theorem c2c1_step_from_nfUStablePred_eq_nfU {z : NormalForm V} :
    NFC2C1StepCtx (α := V) nfUStablePred z → z = nfU := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uStablePredTerm := by
    simpa [nfUStablePred] using hx.symm
  rcases plug_eq_uStablePred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [uStablePredTerm, xAStablePredTerm, A, s, x] at hEq
    nomatch hEq
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
      simpa [Ctx.plug] using hz
    exact eq_nfU_of_c2c1_left_case hL hz'
  ·
    rcases hR with ⟨C', hC, hS⟩
    subst hC
    exact False.elim (no_plug_c2c1_lhs_eq_s C' x0 p z0 hS)

theorem NFStepR_from_nfUStablePred_eq_nfU {z : NormalForm V} :
    NFStepR (α := V) R4 nfUStablePred z → z = nfU := by
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
    exact sqAbsorb_step_from_nfUStablePred_eq_nfU
      (z := z) (show NFSqStepCtx (α := V) nfUStablePred z from hstep)
  ·
    exact sqStable_step_from_nfUStablePred_eq_nfU
      (z := z) (show NFSqStableStepCtx (α := V) nfUStablePred z from hstep)
  ·
    exact decor_step_from_nfUStablePred_eq_nfU
      (z := z) (show NFDecorStepCtx (α := V) nfUStablePred z from hstep)
  ·
    exact c2c1_step_from_nfUStablePred_eq_nfU
      (z := z) (show NFC2C1StepCtx (α := V) nfUStablePred z from hstep)

theorem nfUHolePred_steps_to_nfU :
    NFStepR (α := V) R4 nfUHolePred nfU := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.hole, xATerm, s, ?_, ?_⟩
    ·
      change uHolePredTerm = Ctx.plug Ctx.hole (((xATerm.op s).op (s.op s)))
      simp [Ctx.plug, uHolePredTerm, uTerm, xATerm, A, s, x]
    ·
      change uTerm = Ctx.plug Ctx.hole (xATerm.op s)
      simp [Ctx.plug, uTerm, xATerm, A, s, x]

theorem nfUDecorHolePred_steps_to_nfU :
    NFStepR (α := V) R4 nfUDecorHolePred nfU := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.hole, xATerm, s, ?_, ?_⟩
    ·
      change uDecorHolePredTerm
        = Ctx.plug Ctx.hole ((xATerm.op s).op (s.op (s.op s)))
      simp [Ctx.plug, uDecorHolePredTerm, uTerm, xATerm, A, s, x]
    ·
      change uTerm = Ctx.plug Ctx.hole (xATerm.op s)
      simp [Ctx.plug, uTerm, xATerm, A, s, x]

theorem nfUDecorHolePred_steps_to_nfUHolePred :
    NFStepR (α := V) R4 nfUDecorHolePred nfUHolePred := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.right uTerm (Ctx.right s Ctx.hole), x, x, ?_, ?_⟩
    ·
      change uDecorHolePredTerm
        = Ctx.plug (Ctx.right uTerm (Ctx.right s Ctx.hole))
            (((x.op x).op (x.op x)))
      simp [Ctx.plug, uDecorHolePredTerm, uTerm, A, s, x]
    ·
      change uHolePredTerm
        = Ctx.plug (Ctx.right uTerm (Ctx.right s Ctx.hole))
            (x.op x)
      simp [Ctx.plug, uHolePredTerm, uTerm, A, s, x]

def uHoleAltTerm : Term V := uTerm.op s

private theorem uHoleAlt_not_normal :
    ¬ Normal (α := V) uHoleAltTerm := by
  intro hN
  have hnoC1 : ¬ IsC1Root (α := V) uTerm s :=
    ((Normal_op_iff (α := V) uTerm s).1 hN).2.2.1
  apply hnoC1
  refine ⟨xATerm, ?_⟩
  dsimp [uHoleAltTerm, uTerm, xATerm, A, s, x]

theorem plug_eq_uHolePred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uHolePredTerm) :
    (C = Ctx.hole ∧ r = uHolePredTerm) ∨
    (∃ C', C = Ctx.left C' A ∧ Ctx.plug C' r = uTerm) ∨
    (∃ C', C = Ctx.right uTerm C' ∧ Ctx.plug C' r = A) := by
  simpa [uHolePredTerm] using plug_eq_op_cases C r uTerm A h

theorem no_sqStable_root_eq_uHolePred
    (t u : Term V) :
    ((((t.op u).op (u.op u)).op u)) ≠ uHolePredTerm := by
  intro hEq
  dsimp [uHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq

theorem no_decor_root_eq_uHolePred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uHolePredTerm := by
  intro hEq
  dsimp [uHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  nomatch hEq


theorem c2c1_root_eq_uHolePred_forces_step_eq_uTerm
    {x0 p z0 : Term V}
    (hEq : (((x0.op (p.op z0)).op z0).op (p.op z0)) = uHolePredTerm) :
    ((x0.op (p.op z0)).op z0) = uTerm := by
  dsimp [uHolePredTerm, uTerm, xATerm, A, s, x] at hEq
  injection hEq


theorem sqAbsorb_succ_from_nfUHolePred_eq_nfU {z : NormalForm V} :
    NFSqStepCtx (α := V) nfUHolePred z → z = nfU := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uHolePredTerm := by
    simpa [nfUHolePred] using hx.symm
  rcases plug_eq_uHolePred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    dsimp [uHolePredTerm, uTerm, xATerm, A, s, x] at hEq
    injection hEq with hL hR
    injection hR with hu1 hu2
    subst u
    injection hL with ht hs
    subst t
    apply Subtype.ext
    simpa [nfU, uTerm, xATerm, A, s, x] using hz
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op A := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op A) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) A).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFSqStepCtx (α := V) nfU y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact False.elim (no_NFStepR_from_nfU (z := y) ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_A_cases C' (((t.op u).op (u.op u))) hright with
      h0 | h1 | h2 | h3 | h4 | h5 | h6
    ·
      rcases h0 with ⟨rfl, hEq⟩
      have htu : t.op u = s :=
        sqAbsorb_root_eq_A_forces_tu_eq_s hEq
      have hzVal : z.1 = uHoleAltTerm := by
        rw [htu] at hz
        simpa [uHoleAltTerm, A, s, x, Ctx.plug] using hz
      have : Normal (α := V) uHoleAltTerm := by
        simpa [hzVal] using z.2
      exact False.elim (uHoleAlt_not_normal this)
    ·
      rcases h1 with ⟨_, hs⟩
      exact False.elim (no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs))
    ·
      rcases h2 with ⟨_, hs⟩
      exact False.elim (no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs))
    ·
      rcases h3 with ⟨_, hx⟩
      exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
    ·
      rcases h4 with ⟨_, hx⟩
      exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
    ·
      rcases h5 with ⟨_, hx⟩
      exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
    ·
      rcases h6 with ⟨_, hx⟩
      exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))

theorem no_sqStable_succ_from_nfUHolePred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfUHolePred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uHolePredTerm := by
    simpa [nfUHolePred] using hx.symm
  rcases plug_eq_uHolePred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uHolePred t u hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op A := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op A) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) A).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
    have hy : NFSqStableStepCtx (α := V) nfU y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact no_sqStable_succ_from_nfU (z := y) hy
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact no_plug_sqStable_lhs_eq_A C' t u hright

theorem no_decor_succ_from_nfUHolePred {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfUHolePred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uHolePredTerm := by
    simpa [nfUHolePred] using hx.symm
  rcases plug_eq_uHolePred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_decor_root_eq_uHolePred t u hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op A := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op A) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) A).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFDecorStepCtx (α := V) nfU y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact no_decor_succ_from_nfU (z := y) hy
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact no_plug_decor_lhs_eq_A C' t u hright

theorem c2c1_succ_from_nfUHolePred_eq_nfU {z : NormalForm V} :
    NFC2C1StepCtx (α := V) nfUHolePred z → z = nfU := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uHolePredTerm := by
    simpa [nfUHolePred] using hx.symm
  rcases plug_eq_uHolePred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    have hzVal : z.1 = ((x0.op (p.op z0)).op z0) := by
      simpa [Ctx.plug] using hz
    have hstep : ((x0.op (p.op z0)).op z0) = uTerm :=
      c2c1_root_eq_uHolePred_forces_step_eq_uTerm hEq
    apply Subtype.ext
    rw [hzVal, hstep]
    simp [nfU]
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op A := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op A) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) A).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
    have hy : NFC2C1StepCtx (α := V) nfU y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact False.elim (no_c2c1_succ_from_nfU (z := y) hy)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact False.elim (no_plug_c2c1_lhs_eq_A C' x0 p z0 hright)

theorem NFStepR_from_nfUHolePred_eq_nfU {z : NormalForm V} :
    NFStepR (α := V) R4 nfUHolePred z → z = nfU := by
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
    exact sqAbsorb_succ_from_nfUHolePred_eq_nfU
      (z := z) (show NFSqStepCtx (α := V) nfUHolePred z from hstep)
  ·
    exact False.elim <|
      no_sqStable_succ_from_nfUHolePred
        (z := z) (show NFSqStableStepCtx (α := V) nfUHolePred z from hstep)
  ·
    exact False.elim <|
      no_decor_succ_from_nfUHolePred
        (z := z) (show NFDecorStepCtx (α := V) nfUHolePred z from hstep)
  ·
    exact c2c1_succ_from_nfUHolePred_eq_nfU
      (z := z) (show NFC2C1StepCtx (α := V) nfUHolePred z from hstep)

theorem plug_eq_uDecorHolePred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uDecorHolePredTerm) :
    (C = Ctx.hole ∧ r = uDecorHolePredTerm) ∨
    (∃ C', C = Ctx.left C' (s.op A) ∧ Ctx.plug C' r = uTerm) ∨
    (∃ C', C = Ctx.right uTerm C' ∧ Ctx.plug C' r = s.op A) := by
  simpa [uDecorHolePredTerm] using plug_eq_op_cases C r uTerm (s.op A) h

theorem sqAbsorb_succ_from_nfUDecorHolePred_eq_nfUHolePred {z : NormalForm V} :
    NFSqStepCtx (α := V) nfUDecorHolePred z → z = nfUHolePred := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uDecorHolePredTerm := by
    simpa [nfUDecorHolePred] using hx.symm
  rcases plug_eq_uDecorHolePred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_sqAbsorb_root_eq_uDecorHolePred t u hEq)
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op (s.op A) := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op (s.op A)) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) (s.op A)).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFSqStepCtx (α := V) nfU y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact False.elim (no_NFStepR_from_nfU (z := y) ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sA_rhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hS | hA
    ·
      rcases h0 with ⟨rfl, hEq⟩
      have htu : t.op u = s :=
        sqAbsorb_rhs_eq_sA_forces_tu_eq_s hEq
      have hzVal : z.1 = uHoleAltTerm := by
        rw [htu] at hz
        simpa [uHoleAltTerm, uTerm, A, s, x, Ctx.plug] using hz
      have : Normal (α := V) uHoleAltTerm := by
        simpa [hzVal] using z.2
      exact False.elim (uHoleAlt_not_normal this)
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
        have htu : t.op u = s :=
          sqAbsorb_root_eq_A_forces_tu_eq_s hEq
        have hzVal : z.1 = uHolePredTerm := by
          rw [htu] at hz
          simpa [uHolePredTerm, uTerm, A, s, x, Ctx.plug] using hz
        apply Subtype.ext
        simpa [nfUHolePred] using hzVal
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

theorem no_sqStable_succ_from_nfUDecorHolePred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfUDecorHolePred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uDecorHolePredTerm := by
    simpa [nfUDecorHolePred] using hx.symm
  rcases plug_eq_uDecorHolePred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uDecorHolePred t u hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op (s.op A) := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op (s.op A)) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) (s.op A)).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
    have hy : NFSqStableStepCtx (α := V) nfU y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact no_sqStable_succ_from_nfU (z := y) hy
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

theorem decor_succ_from_nfUDecorHolePred_eq_nfU {z : NormalForm V} :
    NFDecorStepCtx (α := V) nfUDecorHolePred z → z = nfU := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uDecorHolePredTerm := by
    simpa [nfUDecorHolePred] using hx.symm
  rcases plug_eq_uDecorHolePred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    have hstep : t.op u = uTerm :=
      decor_root_eq_uDecorHolePred_forces_step_eq_uTerm hEq
    have hzVal : z.1 = uTerm := by
      rw [hstep] at hz
      simpa [Ctx.plug] using hz
    apply Subtype.ext
    simpa [nfU] using hzVal
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op (s.op A) := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op (s.op A)) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) (s.op A)).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFDecorStepCtx (α := V) nfU y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact False.elim (no_decor_succ_from_nfU (z := y) hy)
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

theorem no_c2c1_succ_from_nfUDecorHolePred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfUDecorHolePred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uDecorHolePredTerm := by
    simpa [nfUDecorHolePred] using hx.symm
  rcases plug_eq_uDecorHolePred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_uDecorHolePred x0 p z0 hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op (s.op A) := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op (s.op A)) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) (s.op A)).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
    have hy : NFC2C1StepCtx (α := V) nfU y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfU] using hleft.symm
    exact no_c2c1_succ_from_nfU (z := y) hy
  ·
    rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sA_rhs_cases C' (((x0.op (p.op z0)).op z0).op (p.op z0)) hright with h0 | hS | hA
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

theorem NFStepR_from_nfUDecorHolePred_cases {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorHolePred z → z = nfU ∨ z = nfUHolePred := by
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
    exact Or.inr <|
      sqAbsorb_succ_from_nfUDecorHolePred_eq_nfUHolePred
        (z := z) (show NFSqStepCtx (α := V) nfUDecorHolePred z from hstep)
  ·
    exact False.elim <|
      no_sqStable_succ_from_nfUDecorHolePred
        (z := z) (show NFSqStableStepCtx (α := V) nfUDecorHolePred z from hstep)
  ·
    exact Or.inl <|
      decor_succ_from_nfUDecorHolePred_eq_nfU
        (z := z) (show NFDecorStepCtx (α := V) nfUDecorHolePred z from hstep)
  ·
    exact False.elim <|
      no_c2c1_succ_from_nfUDecorHolePred
        (z := z) (show NFC2C1StepCtx (α := V) nfUDecorHolePred z from hstep)


def mAltTerm : Term V := vTerm.op s

private theorem mAlt_not_normal :
    ¬ Normal (α := V) mAltTerm := by
  intro hN
  have hnoC1 : ¬ IsC1Root (α := V) vTerm s :=
    ((Normal_op_iff (α := V) vTerm s).1 hN).2.2.1
  apply hnoC1
  refine ⟨x, ?_⟩
  dsimp [mAltTerm, vTerm, s, x]

theorem plug_eq_m_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = mTerm) :
    (C = Ctx.hole ∧ r = mTerm) ∨
    (∃ C', C = Ctx.left C' (s.op vTerm) ∧ Ctx.plug C' r = vTerm) ∨
    (∃ C', C = Ctx.right vTerm C' ∧ Ctx.plug C' r = s.op vTerm) := by
  simpa [mTerm] using plug_eq_op_cases C r vTerm (s.op vTerm) h

private theorem no_sqAbsorb_root_eq_m
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ mTerm := by
  intro hEq
  dsimp [mTerm, vTerm, s, x] at hEq
  nomatch hEq

private theorem no_sqStable_root_eq_m
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ mTerm := by
  intro hEq
  dsimp [mTerm, vTerm, s, x] at hEq
  nomatch hEq

private theorem no_decor_root_eq_m
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ mTerm := by
  intro hEq
  dsimp [mTerm, vTerm, s, x] at hEq
  nomatch hEq

private theorem no_c2c1_root_eq_m
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ mTerm := by
  intro hEq
  dsimp [mTerm, vTerm, s, x] at hEq
  nomatch hEq

private theorem no_c2c1_rhs_root_eq_sv
    (x0 p z0 : Term V) :
    ((x0.op (p.op z0)).op z0) ≠ s.op vTerm := by
  intro hEq
  dsimp [vTerm, s, x] at hEq
  nomatch hEq

theorem no_NFStepR_from_nfM {z : NormalForm V} :
    ¬ NFStepR (α := V) R4 nfM z := by
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
    rcases (show NFSqStepCtx (α := V) nfM z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = mTerm := by
      simpa [nfM] using hx.symm
    rcases plug_eq_m_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_sqAbsorb_root_eq_m t u hEq
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
      have hy : NFSqStepCtx (α := V) nfV y := by
        refine ⟨C', t, u, ?_, rfl⟩
        simpa [nfV] using hleft.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.SqAbsorb, by simp [R4], hy⟩
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact no_sqAbsorb_rhs_root_eq_sv t u hEq
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact no_plug_sqAbsorb_lhs_eq_s C'' t u hs
      ·
        rcases hV with ⟨C'', hC'', hv⟩
        subst hC''
        exact no_plug_sqAbsorb_lhs_eq_vTerm C'' t u hv
  ·
    rcases (show NFSqStableStepCtx (α := V) nfM z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = mTerm := by
      simpa [nfM] using hx.symm
    rcases plug_eq_m_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_sqStable_root_eq_m t u hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op (s.op vTerm) := by
        simpa [Ctx.plug] using hz
      have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op (s.op vTerm)) := by
        simpa [hz'] using z.2
      have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
        ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) (s.op vTerm)).1 hzN).1
      let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
      have hy : NFSqStableStepCtx (α := V) nfV y := by
        refine ⟨C', t, u, ?_, rfl⟩
        simpa [nfV] using hleft.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.SqStable, by simp [R4], hy⟩
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact no_sqStable_rhs_root_eq_sv t u hEq
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact no_plug_sqStable_lhs_eq_s C'' t u hs
      ·
        rcases hV with ⟨C'', hC'', hv⟩
        subst hC''
        exact no_plug_sqStable_lhs_eq_vTerm C'' t u hv
  ·
    rcases (show NFDecorStepCtx (α := V) nfM z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = mTerm := by
      simpa [nfM] using hx.symm
    rcases plug_eq_m_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_decor_root_eq_m t u hEq
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
      have hy : NFDecorStepCtx (α := V) nfV y := by
        refine ⟨C', t, u, ?_, rfl⟩
        simpa [nfV] using hleft.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.Decor, by simp [R4], hy⟩
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        have hstep : t.op u = s :=
          decor_rhs_eq_sv_forces_step_eq_s hEq
        have hzVal : z.1 = mAltTerm := by
          rw [hstep] at hz
          simpa [mAltTerm, mTerm, vTerm, s, x, Ctx.plug] using hz
        have : Normal (α := V) mAltTerm := by
          simpa [hzVal] using z.2
        exact mAlt_not_normal this
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact no_plug_decor_lhs_eq_s C'' t u hs
      ·
        rcases hV with ⟨C'', hC'', hv⟩
        subst hC''
        exact no_plug_decor_lhs_eq_vTerm C'' t u hv
  ·
    rcases (show NFC2C1StepCtx (α := V) nfM z from hstep) with ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = mTerm := by
      simpa [nfM] using hx.symm
    rcases plug_eq_m_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_c2c1_root_eq_m x0 p z0 hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op (s.op vTerm) := by
        simpa [Ctx.plug] using hz
      have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op (s.op vTerm)) := by
        simpa [hz'] using z.2
      have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
        ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) (s.op vTerm)).1 hzN).1
      let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
      have hy : NFC2C1StepCtx (α := V) nfV y := by
        refine ⟨C', x0, p, z0, ?_, rfl⟩
        simpa [nfV] using hleft.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.C2C1, by simp [R4], hy⟩
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' (((x0.op (p.op z0)).op z0).op (p.op z0)) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        injection hEq with hL hR
        dsimp [s, vTerm, x] at hL
        injection hL with hL_left hL_right
        contradiction
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact no_plug_c2c1_lhs_eq_s C'' x0 p z0 hs
      ·
        rcases hV with ⟨C'', hC'', hv⟩
        subst hC''
        exact no_plug_c2c1_lhs_eq_vTerm C'' x0 p z0 hv

theorem nfUDecorRightPred_steps_to_nfM :
    NFStepR (α := V) R4 nfUDecorRightPred nfM := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right x Ctx.hole) (s.op vTerm), x, x, ?_, ?_⟩
    ·
      change uDecorRightPredTerm
        = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) (s.op vTerm))
            (((x.op x).op (x.op x)))
      simp [Ctx.plug, uDecorRightPredTerm, xATerm, vTerm, A, s, x]
    ·
      change mTerm
        = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) (s.op vTerm))
            (x.op x)
      simp [Ctx.plug, mTerm, vTerm, s, x]

theorem eq_nfM_of_left_val {z : NormalForm V} {w : Term V}
    (hz' : z.1 = w.op (s.op vTerm))
    (hw : w = vTerm) : z = nfM := by
  apply Subtype.ext
  rw [hz', hw]
  simp [nfM, mTerm]

theorem NFStepR_from_nfUDecorRightPred_cases {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorRightPred z → z = nfU ∨ z = nfM := by
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
    rcases (show NFSqStepCtx (α := V) nfUDecorRightPred z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uDecorRightPredTerm := by
      simpa [nfUDecorRightPred] using hx.symm
    rcases plug_eq_uDecorRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqAbsorb_root_eq_uDecorRightPred t u hEq)
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
      have hy : NFSqStepCtx (α := V) nfXA y := by
        refine ⟨C', t, u, ?_, rfl⟩
        simpa [nfXA] using hleft.symm
      have hyEq : y = nfV :=
        NFStepR_from_nfXA_eq_nfV
          (z := y) (by exact ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
      have hyVal : y.1 = vTerm := by
        simpa [nfV] using congrArg Subtype.val hyEq
      exact Or.inr (eq_nfM_of_left_val hz' hyVal)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact False.elim (no_sqAbsorb_rhs_root_eq_sv t u hEq)
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact False.elim (no_plug_sqAbsorb_lhs_eq_s C'' t u hs)
      ·
        rcases hV with ⟨C'', hC'', hv⟩
        subst hC''
        exact False.elim (no_plug_sqAbsorb_lhs_eq_vTerm C'' t u hv)
  ·
    rcases (show NFSqStableStepCtx (α := V) nfUDecorRightPred z from hstep) with ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uDecorRightPredTerm := by
      simpa [nfUDecorRightPred] using hx.symm
    rcases plug_eq_uDecorRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqStable_root_eq_uDecorRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op (s.op vTerm) := by
        simpa [Ctx.plug] using hz
      have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op (s.op vTerm)) := by
        simpa [hz'] using z.2
      have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
        ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) (s.op vTerm)).1 hzN).1
      let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
      have hy : NFSqStableStepCtx (α := V) nfXA y := by
        refine ⟨C', t, u, ?_, rfl⟩
        simpa [nfXA] using hleft.symm
      have hyEq : y = nfV :=
        NFStepR_from_nfXA_eq_nfV
          (z := y) (by exact ⟨RuleId.SqStable, by simp [R4], hy⟩)
      have hyVal : y.1 = vTerm := by
        simpa [nfV] using congrArg Subtype.val hyEq
      exact Or.inr (eq_nfM_of_left_val hz' hyVal)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact False.elim (no_sqStable_rhs_root_eq_sv t u hEq)
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact False.elim (no_plug_sqStable_lhs_eq_s C'' t u hs)
      ·
        rcases hV with ⟨C'', hC'', hv⟩
        subst hC''
        exact False.elim (no_plug_sqStable_lhs_eq_vTerm C'' t u hv)
  ·
    rcases (show NFDecorStepCtx (α := V) nfUDecorRightPred z from hstep) with ⟨C, t, u, hx, hz⟩
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
      have hyEq : y = nfV :=
        NFStepR_from_nfXA_eq_nfV
          (z := y) (by exact ⟨RuleId.Decor, by simp [R4], hy⟩)
      have hyVal : y.1 = vTerm := by
        simpa [nfV] using congrArg Subtype.val hyEq
      exact Or.inr (eq_nfM_of_left_val hz' hyVal)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        have hstep : t.op u = s :=
          decor_rhs_eq_sv_forces_step_eq_s hEq
        have hzVal : z.1 = uTerm := by
          rw [hstep] at hz
          simpa [uTerm, xATerm, vTerm, s, x, Ctx.plug] using hz
        exact Or.inl <| by
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
  ·
    rcases (show NFC2C1StepCtx (α := V) nfUDecorRightPred z from hstep) with ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uDecorRightPredTerm := by
      simpa [nfUDecorRightPred] using hx.symm
    rcases plug_eq_uDecorRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_c2c1_root_eq_uDecorRightPred x0 p z0 hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op (s.op vTerm) := by
        simpa [Ctx.plug] using hz
      have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op (s.op vTerm)) := by
        simpa [hz'] using z.2
      have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
        ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) (s.op vTerm)).1 hzN).1
      let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
      have hy : NFC2C1StepCtx (α := V) nfXA y := by
        refine ⟨C', x0, p, z0, ?_, rfl⟩
        simpa [nfXA] using hleft.symm
      have hyEq : y = nfV :=
        NFStepR_from_nfXA_eq_nfV
          (z := y) (by exact ⟨RuleId.C2C1, by simp [R4], hy⟩)
      have hyVal : y.1 = vTerm := by
        simpa [nfV] using congrArg Subtype.val hyEq
      exact Or.inr (eq_nfM_of_left_val hz' hyVal)
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      rcases plug_eq_sv_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hright with h0 | hS | hV
      ·
        rcases h0 with ⟨rfl, hEq⟩
        exact False.elim (no_c2c1_lhs_root_eq_sv x0 p z0 hEq)
      ·
        rcases hS with ⟨C'', hC'', hs⟩
        subst hC''
        exact False.elim (no_plug_c2c1_lhs_eq_s C'' x0 p z0 hs)
      ·
        rcases hV with ⟨C'', hC'', hv⟩
        subst hC''
        exact False.elim (no_plug_c2c1_lhs_eq_vTerm C'' x0 p z0 hv)

end KernelStableHoleBridge

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
