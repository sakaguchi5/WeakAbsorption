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

section KernelDecor

def nfXADecorRightPred : NormalForm V :=
  ⟨xADecorRightSPredTerm, xADecorRightSPred_normal⟩

theorem plug_eq_xADecorRightPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = xADecorRightSPredTerm) :
    (C = Ctx.hole ∧ r = xADecorRightSPredTerm) ∨
    (∃ C', C = Ctx.left C' (s.op (s.op vTerm)) ∧ Ctx.plug C' r = x) ∨
    (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = s.op (s.op vTerm)) := by
  simpa [xADecorRightSPredTerm] using plug_eq_op_cases C r x (s.op (s.op vTerm)) h

theorem plug_eq_ssv_rhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = s.op (s.op vTerm)) :
    (C = Ctx.hole ∧ r = s.op (s.op vTerm)) ∨
    (∃ C', C = Ctx.left C' (s.op vTerm) ∧ Ctx.plug C' r = s) ∨
    (∃ C', C = Ctx.right s C' ∧ Ctx.plug C' r = s.op vTerm) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r0 =>
      dsimp [Ctx.plug, s, vTerm, x] at h
      injection h with hL hR
      subst hR
      exact Or.inr (Or.inl ⟨C, rfl, by simpa [s] using hL⟩)
  | right l C =>
      dsimp [Ctx.plug, s, vTerm, x] at h
      injection h with hL hR
      subst hL
      exact Or.inr (Or.inr ⟨C, rfl, by simpa [s, vTerm, x] using hR⟩)

private theorem no_sqAbsorb_root_xADecorRightPred :
    NoRootInstance sqAbsorbPat xADecorRightSPredTerm := by
  simpa [xADecorRightSPredTerm] using
    (no_sqAbsorb_root_x_left (q := s.op (s.op (x.op s))))

private theorem no_sqStable_root_xADecorRightPred :
    NoRootInstance sqStablePat xADecorRightSPredTerm := by
  simpa [xADecorRightSPredTerm] using
    (no_sqStable_root_x_left (q := s.op (s.op (x.op s))))

private theorem no_decor_root_xADecorRightPred :
    NoRootInstance decorPat xADecorRightSPredTerm := by
  simpa [xADecorRightSPredTerm] using
    (no_decor_root_x_left (q := s.op (s.op (x.op s))))

private theorem no_c2c1_root_xADecorRightPred :
    NoRootInstance c2c1Pat xADecorRightSPredTerm := by
  simpa [xADecorRightSPredTerm] using
    (no_c2c1_root_x_left (q := s.op (s.op (x.op s))))

theorem no_sqAbsorb_root_eq_xADecorRightPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xADecorRightSPredTerm := by
  exact no_sqAbsorb_root_eq_of_no_instance no_sqAbsorb_root_xADecorRightPred t u

theorem no_sqStable_root_eq_xADecorRightPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xADecorRightSPredTerm := by
  exact no_sqStable_root_eq_of_no_instance no_sqStable_root_xADecorRightPred t u

theorem no_decor_root_eq_xADecorRightPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xADecorRightSPredTerm := by
  exact no_decor_root_eq_of_no_instance no_decor_root_xADecorRightPred t u

theorem no_c2c1_root_eq_xADecorRightPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xADecorRightSPredTerm := by
  exact no_c2c1_root_eq_of_no_instance no_c2c1_root_xADecorRightPred x0 p z0


private theorem eq_nfXA_of_right_ss_val {z : NormalForm V} {w : Term V}
    (hz' : z.1 = x.op (s.op w))
    (hw : w = s) : z = nfXA := by
  apply Subtype.ext
  rw [hw] at hz'
  simpa [nfXA, xATerm, A, s, x] using hz'

private theorem no_sqAbsorb_rhs_root_eq_ssv
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ s.op (s.op vTerm) := by
  intro hEq
  dsimp [s, vTerm, x] at hEq
  cases hEq

private theorem no_sqStable_rhs_root_eq_ssv
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ s.op (s.op vTerm) := by
  intro hEq
  dsimp [s, vTerm, x] at hEq
  cases hEq

private theorem no_decor_rhs_root_eq_ssv
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ s.op (s.op vTerm) := by
  intro hEq
  dsimp [s, vTerm, x] at hEq
  cases hEq

private theorem no_c2c1_rhs_root_eq_ssv
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ s.op (s.op vTerm) := by
  intro hEq
  dsimp [s, vTerm, x] at hEq
  cases hEq

theorem sqAbsorb_right_succ_from_nfXADecorRightPred_false
    {z : NormalForm V} {C' : Ctx V} {t u : Term V}
    (hright : Ctx.plug C' (((t.op u).op (u.op u))) = s.op (s.op vTerm))
    (hz : z.1 = x.op (Ctx.plug C' (t.op u))) :
    False := by
  rcases plug_eq_ssv_rhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hS | hSV
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqAbsorb_rhs_root_eq_ssv t u hEq
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact no_plug_sqAbsorb_lhs_eq_s C'' t u hs
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' (((t.op u).op (u.op u))) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_sqAbsorb_rhs_root_eq_sv t u hEq
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact no_plug_sqAbsorb_lhs_eq_s C''' t u hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      have hz' : z.1 = x.op (s.op (s.op (Ctx.plug C''' (t.op u)))) := by
        simpa [Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op (s.op (s.op (Ctx.plug C''' (t.op u))))) := by
        simpa [hz'] using z.2
      have hrightN : Normal (α := V) (Ctx.plug C''' (t.op u)) := by
        have hssN : Normal (α := V) (s.op (s.op (Ctx.plug C''' (t.op u)))) :=
          ((Normal_op_iff (α := V) x (s.op (s.op (Ctx.plug C''' (t.op u))))).1 hzN).2.1
        have hsN : Normal (α := V) (s.op (Ctx.plug C''' (t.op u))) :=
          ((Normal_op_iff (α := V) s (s.op (Ctx.plug C''' (t.op u)))).1 hssN).2.1
        exact ((Normal_op_iff (α := V) s (Ctx.plug C''' (t.op u))).1 hsN).2.1
      let y : NormalForm V := ⟨Ctx.plug C''' (t.op u), hrightN⟩
      have hy : NFSqStepCtx (α := V) nfV y := by
        refine ⟨C''', t, u, ?_, rfl⟩
        simpa [nfV] using hv.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.SqAbsorb, by simp [R4], hy⟩


theorem sqStable_right_succ_from_nfXADecorRightPred_false
    {z : NormalForm V} {C' : Ctx V} {t u : Term V}
    (hright : Ctx.plug C' ((((t.op u).op (u.op u)).op u)) = s.op (s.op vTerm))
    (hz : z.1 = x.op (Ctx.plug C' ((t.op u).op (u.op u)))) :
    False := by
  rcases plug_eq_ssv_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hS | hSV
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_rhs_root_eq_ssv t u hEq
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact no_plug_sqStable_lhs_eq_s C'' t u hs
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' ((((t.op u).op (u.op u)).op u)) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_sqStable_rhs_root_eq_sv t u hEq
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact no_plug_sqStable_lhs_eq_s C''' t u hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      have hz' : z.1 = x.op (s.op (s.op (Ctx.plug C''' ((t.op u).op (u.op u))))) := by
        simpa [Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op (s.op (s.op (Ctx.plug C''' ((t.op u).op (u.op u)))))) := by
        simpa [hz'] using z.2
      have hrightN : Normal (α := V) (Ctx.plug C''' ((t.op u).op (u.op u))) := by
        have hssN : Normal (α := V) (s.op (s.op (Ctx.plug C''' ((t.op u).op (u.op u))))) :=
          ((Normal_op_iff (α := V) x (s.op (s.op (Ctx.plug C''' ((t.op u).op (u.op u)))))).1 hzN).2.1
        have hsN : Normal (α := V) (s.op (Ctx.plug C''' ((t.op u).op (u.op u)))) :=
          ((Normal_op_iff (α := V) s (s.op (Ctx.plug C''' ((t.op u).op (u.op u))))).1 hssN).2.1
        exact ((Normal_op_iff (α := V) s (Ctx.plug C''' ((t.op u).op (u.op u)))).1 hsN).2.1
      let y : NormalForm V := ⟨Ctx.plug C''' ((t.op u).op (u.op u)), hrightN⟩
      have hy : NFSqStableStepCtx (α := V) nfV y := by
        refine ⟨C''', t, u, ?_, rfl⟩
        simpa [nfV] using hv.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.SqStable, by simp [R4], hy⟩

private theorem decor_right_succ_from_nfXADecorRightPred_eq_nfXA
    {z : NormalForm V} {C' : Ctx V} {t u : Term V}
    (hright : Ctx.plug C' ((t.op u).op (u.op (u.op u))) = s.op (s.op vTerm))
    (hz : z.1 = x.op (Ctx.plug C' (t.op u))) :
    z = nfXA := by
  rcases plug_eq_ssv_rhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hS | hSV
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim <| no_decor_rhs_root_eq_ssv t u hEq
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact False.elim <| no_plug_decor_lhs_eq_s C'' t u hs
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' ((t.op u).op (u.op (u.op u))) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      have htu : t.op u = s := decor_rhs_eq_sv_forces_step_eq_s hEq
      have hz' : z.1 = x.op (s.op (t.op u)) := by
        simpa [Ctx.plug, x, s] using hz
      exact eq_nfXA_of_right_ss_val hz' htu
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact False.elim <| no_plug_decor_lhs_eq_s C''' t u hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      have hz' : z.1 = x.op (s.op (s.op (Ctx.plug C''' (t.op u)))) := by
        simpa [Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op (s.op (s.op (Ctx.plug C''' (t.op u))))) := by
        simpa [hz'] using z.2
      have hrightN : Normal (α := V) (Ctx.plug C''' (t.op u)) := by
        have hssN : Normal (α := V) (s.op (s.op (Ctx.plug C''' (t.op u)))) :=
          ((Normal_op_iff (α := V) x (s.op (s.op (Ctx.plug C''' (t.op u))))).1 hzN).2.1
        have hsN : Normal (α := V) (s.op (Ctx.plug C''' (t.op u))) :=
          ((Normal_op_iff (α := V) s (s.op (Ctx.plug C''' (t.op u)))).1 hssN).2.1
        exact ((Normal_op_iff (α := V) s (Ctx.plug C''' (t.op u))).1 hsN).2.1
      let y : NormalForm V := ⟨Ctx.plug C''' (t.op u), hrightN⟩
      have hy : NFDecorStepCtx (α := V) nfV y := by
        refine ⟨C''', t, u, ?_, rfl⟩
        simpa [nfV] using hv.symm
      exact False.elim <|
        no_NFStepR_from_nfV (z := y) ⟨RuleId.Decor, by simp [R4], hy⟩

theorem c2c1_right_succ_from_nfXADecorRightPred_false
    {z : NormalForm V} {C' : Ctx V} {x0 p z0 : Term V}
    (hright : Ctx.plug C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) = s.op (s.op vTerm))
    (hz : z.1 = x.op (Ctx.plug C' ((x0.op (p.op z0)).op z0))) :
    False := by
  rcases plug_eq_ssv_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hright with h0 | hS | hSV
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_rhs_root_eq_ssv x0 p z0 hEq
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact no_plug_c2c1_lhs_eq_s C'' x0 p z0 hs
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_c2c1_lhs_root_eq_sv x0 p z0 hEq
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact no_plug_c2c1_lhs_eq_s C''' x0 p z0 hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      let w : Term V := Ctx.plug C''' ((x0.op (p.op z0)).op z0)
      have hz' : z.1 = x.op (s.op (s.op w)) := by
        simpa [w, Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op (s.op (s.op w))) := by
        simpa [hz', w] using z.2
      have hssN : Normal (α := V) (s.op (s.op w)) :=
        ((Normal_op_iff (α := V) x (s.op (s.op w))).1 hzN).2.1
      have hsN : Normal (α := V) (s.op w) :=
        ((Normal_op_iff (α := V) s (s.op w)).1 hssN).2.1
      have hwN : Normal (α := V) w :=
        ((Normal_op_iff (α := V) s w).1 hsN).2.1
      let y : NormalForm V := ⟨w, hwN⟩
      have hy : NFC2C1StepCtx (α := V) nfV y := by
        refine ⟨C''', x0, p, z0, ?_, rfl⟩
        simpa [nfV, w] using hv.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.C2C1, by simp [R4], hy⟩

theorem NFStepR_from_nfXADecorRightPred_eq_nfXA {z : NormalForm V} :
    NFStepR (α := V) R4 nfXADecorRightPred z → z = nfXA := by
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
    rcases (show NFSqStepCtx (α := V) nfXADecorRightPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = xADecorRightSPredTerm := by
      simpa [nfXADecorRightPred] using hx.symm
    rcases plug_eq_xADecorRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_sqAbsorb_root_eq_xADecorRightPred t u hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_sqAbsorb_lhs_eq_x C' t u hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact False.elim <| sqAbsorb_right_succ_from_nfXADecorRightPred_false hright hz
  ·
    rcases (show NFSqStableStepCtx (α := V) nfXADecorRightPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xADecorRightSPredTerm := by
      simpa [nfXADecorRightPred] using hx.symm
    rcases plug_eq_xADecorRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_sqStable_root_eq_xADecorRightPred t u hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_sqStable_lhs_eq_x C' t u hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact False.elim <| sqStable_right_succ_from_nfXADecorRightPred_false hright hz
  ·
    rcases (show NFDecorStepCtx (α := V) nfXADecorRightPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xADecorRightSPredTerm := by
      simpa [nfXADecorRightPred] using hx.symm
    rcases plug_eq_xADecorRightPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_decor_root_eq_xADecorRightPred t u hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_decor_lhs_eq_x C' t u hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact decor_right_succ_from_nfXADecorRightPred_eq_nfXA hright hz
  ·
    rcases (show NFC2C1StepCtx (α := V) nfXADecorRightPred z from hstep) with
      ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xADecorRightSPredTerm := by
      simpa [nfXADecorRightPred] using hx.symm
    rcases plug_eq_xADecorRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_c2c1_root_eq_xADecorRightPred x0 p z0 hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact False.elim <| c2c1_right_succ_from_nfXADecorRightPred_false hright hz

theorem plug_eq_uDecorLiftRightPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uDecorLiftRightSPredTerm) :
    (C = Ctx.hole ∧ r = uDecorLiftRightSPredTerm) ∨
    (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xADecorRightSPredTerm) ∨
    (∃ C', C = Ctx.right xADecorRightSPredTerm C' ∧ Ctx.plug C' r = s) := by
  simpa [uDecorLiftRightSPredTerm] using plug_eq_op_cases C r xADecorRightSPredTerm s h

private theorem sqAbsorb_root_uDecorLiftRightPred_forces_u_eq_x :
    RootMatchForces sqAbsorbPat uDecorLiftRightSPredTerm
      (fun σ => σ 1 = x) := by
  intro σ hEq
  dsimp [sqAbsorbPat, Pat.inst, uDecorLiftRightSPredTerm, xADecorRightSPredTerm, vTerm, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem sqAbsorb_root_uDecorLiftRightPred_refute_of_u_eq_x :
    ∀ σ, σ 1 = x → Pat.inst σ sqAbsorbPat ≠ uDecorLiftRightSPredTerm := by
  intro σ hux hEq
  dsimp [sqAbsorbPat, Pat.inst] at hEq
  rw [hux] at hEq
  dsimp [uDecorLiftRightSPredTerm, xADecorRightSPredTerm, vTerm, s, x] at hEq
  injection hEq with hL hR
  injection hL with ht hu
  cases hu

def sqAbsorbRF_uDecorLiftRightPred :
    SqAbsorbRightForcingWitness uDecorLiftRightSPredTerm where
  Φ := fun σ => σ 1 = x
  forces := sqAbsorb_root_uDecorLiftRightPred_forces_u_eq_x
  refute := sqAbsorb_root_uDecorLiftRightPred_refute_of_u_eq_x

theorem no_sqAbsorb_root_eq_uDecorLiftRightPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorLiftRightSPredTerm := by
  exact no_sqAbsorb_root_eq_of_rightForcing sqAbsorbRF_uDecorLiftRightPred t u

theorem no_sqStable_root_uDecorLiftRightPred :
    SqStableGlobalNoRootWitness uDecorLiftRightSPredTerm := by
  intro σ hEq
  dsimp [sqStablePat, Pat.inst, uDecorLiftRightSPredTerm, xADecorRightSPredTerm, vTerm, s, x] at hEq
  nomatch hEq

theorem no_sqStable_root_eq_uDecorLiftRightPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uDecorLiftRightSPredTerm := by
  exact no_sqStable_root_eq_of_globalNoRoot no_sqStable_root_uDecorLiftRightPred t u

theorem no_decor_root_uDecorLiftRightPred :
    NoRootInstance decorPat uDecorLiftRightSPredTerm := by
  intro σ hEq
  dsimp [decorPat, Pat.inst, uDecorLiftRightSPredTerm, xADecorRightSPredTerm, vTerm, s, x] at hEq
  injection hEq with hL hR
  injection hR with ht hu
  cases hu

theorem no_decor_root_eq_uDecorLiftRightPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uDecorLiftRightSPredTerm := by
  exact no_decor_root_eq_of_rightShell no_decor_root_uDecorLiftRightPred t u

theorem no_c2c1_root_uDecorLiftRightPred :
    C2C1LeftShellWitness uDecorLiftRightSPredTerm := by
  intro σ hEq
  dsimp [c2c1Pat, Pat.inst, uDecorLiftRightSPredTerm, xADecorRightSPredTerm, vTerm, s, x] at hEq
  injection hEq with hL hR
  cases hL

theorem no_c2c1_root_eq_uDecorLiftRightPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uDecorLiftRightSPredTerm := by
  exact no_c2c1_root_eq_of_leftShell no_c2c1_root_uDecorLiftRightPred x0 p z0

theorem nfXADecorRightPred_steps_to_nfXA :
    NFStepR (α := V) R4 nfXADecorRightPred nfXA := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.right x (Ctx.right s Ctx.hole), x, x, ?_, ?_⟩
    ·
      change xADecorRightSPredTerm
        = Ctx.plug (Ctx.right x (Ctx.right s Ctx.hole))
            (((x.op x).op (x.op (x.op x))))
      simp [Ctx.plug, xADecorRightSPredTerm, s, x]
    ·
      change xATerm = Ctx.plug (Ctx.right x (Ctx.right s Ctx.hole)) (x.op x)
      simp [Ctx.plug, xATerm, A, s, x]

private theorem eq_nfU_of_sqAbsorb_left_case_from_xADecorRight {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' (((t.op u).op (u.op u))) = xADecorRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFSqStepCtx (α := V) nfXADecorRightPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXADecorRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_sqStable_left_case_from_xADecorRight {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((((t.op u).op (u.op u)).op u)) = xADecorRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
  have hy : NFSqStableStepCtx (α := V) nfXADecorRightPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXADecorRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqStable, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_decor_left_case_from_xADecorRight {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((t.op u).op (u.op (u.op u))) = xADecorRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFDecorStepCtx (α := V) nfXADecorRightPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXADecorRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.Decor, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

theorem eq_nfU_of_c2c1_left_case_from_xADecorRight {z : NormalForm V}
    {C' : Ctx V} {x0 p z0 : Term V}
    (hL : Ctx.plug C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xADecorRightSPredTerm)
    (hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
  have hy : NFC2C1StepCtx (α := V) nfXADecorRightPred y := by
    refine ⟨C', x0, p, z0, ?_, rfl⟩
    simpa [nfXADecorRightPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorRightPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.C2C1, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

theorem NFStepR_from_nfUDecorLiftRightSPred_eq_nfU {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorLiftRightSPred z → z = nfU := by
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
    rcases (show NFSqStepCtx (α := V) nfUDecorLiftRightSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uDecorLiftRightSPredTerm := by
      simpa [nfUDecorLiftRightSPred] using hx.symm
    rcases plug_eq_uDecorLiftRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqAbsorb_root_eq_uDecorLiftRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_sqAbsorb_left_case_from_xADecorRight hL hz'
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
    rcases (show NFSqStableStepCtx (α := V) nfUDecorLiftRightSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uDecorLiftRightSPredTerm := by
      simpa [nfUDecorLiftRightSPred] using hx.symm
    rcases plug_eq_uDecorLiftRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqStable_root_eq_uDecorLiftRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_sqStable_left_case_from_xADecorRight hL hz'
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
    rcases (show NFDecorStepCtx (α := V) nfUDecorLiftRightSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uDecorLiftRightSPredTerm := by
      simpa [nfUDecorLiftRightSPred] using hx.symm
    rcases plug_eq_uDecorLiftRightPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_decor_root_eq_uDecorLiftRightPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_decor_left_case_from_xADecorRight hL hz'
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
    rcases (show NFC2C1StepCtx (α := V) nfUDecorLiftRightSPred z from hstep) with
      ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uDecorLiftRightSPredTerm := by
      simpa [nfUDecorLiftRightSPred] using hx.symm
    rcases plug_eq_uDecorLiftRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_c2c1_root_eq_uDecorLiftRightPred x0 p z0 hEq)
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_c2c1_left_case_from_xADecorRight hL hz'
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


def nfXADecorLeftPred : NormalForm V :=
  ⟨xADecorLeftSPredTerm, xADecorLeftSPred_normal⟩






theorem plug_eq_xADecorLeftPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = xADecorLeftSPredTerm) :
    (C = Ctx.hole ∧ r = xADecorLeftSPredTerm) ∨
    (∃ C', C = Ctx.left C' ((s.op vTerm).op s) ∧ Ctx.plug C' r = x) ∨
    (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = (s.op vTerm).op s) := by
  simpa [xADecorLeftSPredTerm] using plug_eq_op_cases C r x ((s.op vTerm).op s) h

theorem plug_eq_svs_rhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = ((s.op vTerm).op s)) :
    (C = Ctx.hole ∧ r = ((s.op vTerm).op s)) ∨
    (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = (s.op vTerm)) ∨
    (∃ C', C = Ctx.right (s.op vTerm) C' ∧ Ctx.plug C' r = s) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r0 =>
      dsimp [Ctx.plug, s, vTerm, x] at h
      injection h with hL hR
      subst hR
      exact Or.inr <| Or.inl ⟨C, rfl, by simpa [s, vTerm, x] using hL⟩
  | right l C =>
      dsimp [Ctx.plug, s, vTerm, x] at h
      injection h with hL hR
      subst hL
      exact Or.inr <| Or.inr ⟨C, rfl, by simpa [s, vTerm, x] using hR⟩

private theorem no_sqAbsorb_root_xADecorLeftPred :
    NoRootInstance sqAbsorbPat xADecorLeftSPredTerm := by
  simpa [xADecorLeftSPredTerm] using
    (no_sqAbsorb_root_x_left (q := ((s.op (x.op s)).op s)))

private theorem no_sqStable_root_xADecorLeftPred :
    NoRootInstance sqStablePat xADecorLeftSPredTerm := by
  simpa [xADecorLeftSPredTerm] using
    (no_sqStable_root_x_left (q := ((s.op (x.op s)).op s)))

private theorem no_decor_root_xADecorLeftPred :
    NoRootInstance decorPat xADecorLeftSPredTerm := by
  simpa [xADecorLeftSPredTerm] using
    (no_decor_root_x_left (q := ((s.op (x.op s)).op s)))

private theorem no_c2c1_root_xADecorLeftPred :
    NoRootInstance c2c1Pat xADecorLeftSPredTerm := by
  simpa [xADecorLeftSPredTerm] using
    (no_c2c1_root_x_left (q := ((s.op (x.op s)).op s)))

theorem no_sqAbsorb_root_eq_xADecorLeftPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xADecorLeftSPredTerm := by
  exact no_sqAbsorb_root_eq_of_no_instance no_sqAbsorb_root_xADecorLeftPred t u

theorem no_sqStable_root_eq_xADecorLeftPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xADecorLeftSPredTerm := by
  exact no_sqStable_root_eq_of_no_instance no_sqStable_root_xADecorLeftPred t u

theorem no_decor_root_eq_xADecorLeftPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xADecorLeftSPredTerm := by
  exact no_decor_root_eq_of_no_instance no_decor_root_xADecorLeftPred t u

theorem no_c2c1_root_eq_xADecorLeftPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xADecorLeftSPredTerm := by
  exact no_c2c1_root_eq_of_no_instance no_c2c1_root_xADecorLeftPred x0 p z0

private theorem no_sqAbsorb_rhs_root_eq_svs
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ ((s.op vTerm).op s) := by
  intro hEq
  dsimp [s, vTerm, x] at hEq
  nomatch hEq

private theorem no_sqStable_rhs_root_eq_svs
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ ((s.op vTerm).op s) := by
  intro hEq
  dsimp [vTerm, s, x] at hEq
  nomatch hEq

private theorem no_decor_rhs_root_eq_svs
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ ((s.op vTerm).op s) := by
  intro hEq
  dsimp [vTerm, s, x] at hEq
  nomatch hEq

private theorem no_c2c1_rhs_root_eq_svs
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ ((s.op vTerm).op s) := by
  intro hEq
  dsimp [s, vTerm, x] at hEq
  nomatch hEq

theorem sqAbsorb_right_succ_from_nfXADecorLeftPred_false
    {z : NormalForm V} {C' : Ctx V} {t u : Term V}
    (hright : Ctx.plug C' (((t.op u).op (u.op u))) = ((s.op vTerm).op s))
    (hz : z.1 = x.op (Ctx.plug C' (t.op u))) :
    False := by
  rcases plug_eq_svs_rhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hSV | hS
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqAbsorb_rhs_root_eq_svs t u hEq
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' (((t.op u).op (u.op u))) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_sqAbsorb_rhs_root_eq_sv t u hEq
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact no_plug_sqAbsorb_lhs_eq_s C''' t u hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      have hz' : z.1 = x.op ((s.op (Ctx.plug C''' (t.op u))).op s) := by
        simpa [Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op ((s.op (Ctx.plug C''' (t.op u))).op s)) := by
        simpa [hz'] using z.2
      have hsN : Normal (α := V) ((s.op (Ctx.plug C''' (t.op u))).op s) :=
        ((Normal_op_iff (α := V) x ((s.op (Ctx.plug C''' (t.op u))).op s)).1 hzN).2.1
      have hmidN : Normal (α := V) (s.op (Ctx.plug C''' (t.op u))) := by
        exact ((Normal_op_iff (α := V) (s.op (Ctx.plug C''' (t.op u))) s).1 hsN).1
      have hrightN : Normal (α := V) (Ctx.plug C''' (t.op u)) := by
        exact ((Normal_op_iff (α := V) s (Ctx.plug C''' (t.op u))).1 hmidN).2.1
      let y : NormalForm V := ⟨Ctx.plug C''' (t.op u), hrightN⟩
      have hy : NFSqStepCtx (α := V) nfV y := by
        refine ⟨C''', t, u, ?_, rfl⟩
        simpa [nfV] using hv.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.SqAbsorb, by simp [R4], hy⟩
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact no_plug_sqAbsorb_lhs_eq_s C'' t u hs

theorem sqStable_right_succ_from_nfXADecorLeftPred_false
    {z : NormalForm V} {C' : Ctx V} {t u : Term V}
    (hright : Ctx.plug C' ((((t.op u).op (u.op u)).op u)) = ((s.op vTerm).op s))
    (hz : z.1 = x.op (Ctx.plug C' ((t.op u).op (u.op u)))) :
    False := by
  rcases plug_eq_svs_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hSV | hS
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_rhs_root_eq_svs t u hEq
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' ((((t.op u).op (u.op u)).op u)) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_sqStable_rhs_root_eq_sv t u hEq
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact no_plug_sqStable_lhs_eq_s C''' t u hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      have hz' : z.1 = x.op ((s.op (Ctx.plug C''' ((t.op u).op (u.op u)))).op s) := by
        simpa [Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op ((s.op (Ctx.plug C''' ((t.op u).op (u.op u)))).op s)) := by
        simpa [hz'] using z.2
      have hsN : Normal (α := V) ((s.op (Ctx.plug C''' ((t.op u).op (u.op u)))).op s) :=
        ((Normal_op_iff (α := V) x ((s.op (Ctx.plug C''' ((t.op u).op (u.op u)))).op s)).1 hzN).2.1
      have hmidN : Normal (α := V) (s.op (Ctx.plug C''' ((t.op u).op (u.op u)))) := by
        exact ((Normal_op_iff (α := V) (s.op (Ctx.plug C''' ((t.op u).op (u.op u)))) s).1 hsN).1
      have hrightN : Normal (α := V) (Ctx.plug C''' ((t.op u).op (u.op u))) := by
        exact ((Normal_op_iff (α := V) s (Ctx.plug C''' ((t.op u).op (u.op u)))).1 hmidN).2.1
      let y : NormalForm V := ⟨Ctx.plug C''' ((t.op u).op (u.op u)), hrightN⟩
      have hy : NFSqStableStepCtx (α := V) nfV y := by
        refine ⟨C''', t, u, ?_, rfl⟩
        simpa [nfV] using hv.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.SqStable, by simp [R4], hy⟩
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact no_plug_sqStable_lhs_eq_s C'' t u hs

theorem decor_right_succ_from_nfXADecorLeftPred_eq_nfXA
    {z : NormalForm V} {C' : Ctx V} {t u : Term V}
    (hright : Ctx.plug C' ((t.op u).op (u.op (u.op u))) = ((s.op vTerm).op s))
    (hz : z.1 = x.op (Ctx.plug C' (t.op u))) :
    z = nfXA := by
  rcases plug_eq_svs_rhs_cases C' ((t.op u).op (u.op (u.op u))) hright with h0 | hSV | hS
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact False.elim <| no_decor_rhs_root_eq_svs t u hEq
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' ((t.op u).op (u.op (u.op u))) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      have htu : t.op u = s := decor_rhs_eq_sv_forces_step_eq_s hEq
      have hz' : z.1 = x.op ((t.op u).op s) := by
        simpa [Ctx.plug, x, s] using hz
      apply Subtype.ext
      rw [htu] at hz'
      simpa [nfXA, xATerm, A, s, x] using hz'
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact False.elim <| no_plug_decor_lhs_eq_s C''' t u hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      have hz' : z.1 = x.op ((s.op (Ctx.plug C''' (t.op u))).op s) := by
        simpa [Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op ((s.op (Ctx.plug C''' (t.op u))).op s)) := by
        simpa [hz'] using z.2
      have hsN : Normal (α := V) ((s.op (Ctx.plug C''' (t.op u))).op s) :=
        ((Normal_op_iff (α := V) x ((s.op (Ctx.plug C''' (t.op u))).op s)).1 hzN).2.1
      have hmidN : Normal (α := V) (s.op (Ctx.plug C''' (t.op u))) := by
        exact ((Normal_op_iff (α := V) (s.op (Ctx.plug C''' (t.op u))) s).1 hsN).1
      have hrightN : Normal (α := V) (Ctx.plug C''' (t.op u)) := by
        exact ((Normal_op_iff (α := V) s (Ctx.plug C''' (t.op u))).1 hmidN).2.1
      let y : NormalForm V := ⟨Ctx.plug C''' (t.op u), hrightN⟩
      have hy : NFDecorStepCtx (α := V) nfV y := by
        refine ⟨C''', t, u, ?_, rfl⟩
        simpa [nfV] using hv.symm
      exact False.elim <|
        no_NFStepR_from_nfV (z := y) ⟨RuleId.Decor, by simp [R4], hy⟩
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact False.elim <| no_plug_decor_lhs_eq_s C'' t u hs

theorem c2c1_right_succ_from_nfXADecorLeftPred_false
    {z : NormalForm V} {C' : Ctx V} {x0 p z0 : Term V}
    (hright : Ctx.plug C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) = ((s.op vTerm).op s))
    (hz : z.1 = x.op (Ctx.plug C' ((x0.op (p.op z0)).op z0))) :
    False := by
  rcases plug_eq_svs_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hright with h0 | hSV | hS
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_rhs_root_eq_svs x0 p z0 hEq
  ·
    rcases hSV with ⟨C'', hC'', hsv⟩
    subst hC''
    rcases plug_eq_sv_rhs_cases C'' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hsv with h0 | hS | hV
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact no_c2c1_lhs_root_eq_sv x0 p z0 hEq
    ·
      rcases hS with ⟨C''', hC''', hs⟩
      subst hC'''
      exact no_plug_c2c1_lhs_eq_s C''' x0 p z0 hs
    ·
      rcases hV with ⟨C''', hC''', hv⟩
      subst hC'''
      have hz' : z.1 = x.op ((s.op (Ctx.plug C''' ((x0.op (p.op z0)).op z0))).op s) := by
        simpa [Ctx.plug, x, s] using hz
      have hzN : Normal (α := V) (x.op ((s.op (Ctx.plug C''' ((x0.op (p.op z0)).op z0))).op s)) := by
        simpa [hz'] using z.2
      have hsN : Normal (α := V) ((s.op (Ctx.plug C''' ((x0.op (p.op z0)).op z0))).op s) :=
        ((Normal_op_iff (α := V) x ((s.op (Ctx.plug C''' ((x0.op (p.op z0)).op z0))).op s)).1 hzN).2.1
      have hmidN : Normal (α := V) (s.op (Ctx.plug C''' ((x0.op (p.op z0)).op z0))) := by
        exact ((Normal_op_iff (α := V) (s.op (Ctx.plug C''' ((x0.op (p.op z0)).op z0))) s).1 hsN).1
      have hrightN : Normal (α := V) (Ctx.plug C''' ((x0.op (p.op z0)).op z0)) := by
        exact ((Normal_op_iff (α := V) s (Ctx.plug C''' ((x0.op (p.op z0)).op z0))).1 hmidN).2.1
      let y : NormalForm V := ⟨Ctx.plug C''' ((x0.op (p.op z0)).op z0), hrightN⟩
      have hy : NFC2C1StepCtx (α := V) nfV y := by
        refine ⟨C''', x0, p, z0, ?_, rfl⟩
        simpa [nfV] using hv.symm
      exact no_NFStepR_from_nfV (z := y) ⟨RuleId.C2C1, by simp [R4], hy⟩
  ·
    rcases hS with ⟨C'', hC'', hs⟩
    subst hC''
    exact no_plug_c2c1_lhs_eq_s C'' x0 p z0 hs

theorem NFStepR_from_nfXADecorLeftPred_eq_nfXA {z : NormalForm V} :
    NFStepR (α := V) R4 nfXADecorLeftPred z → z = nfXA := by
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
    rcases (show NFSqStepCtx (α := V) nfXADecorLeftPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = xADecorLeftSPredTerm := by
      simpa [nfXADecorLeftPred] using hx.symm
    rcases plug_eq_xADecorLeftPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_sqAbsorb_root_eq_xADecorLeftPred t u hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_sqAbsorb_lhs_eq_x C' t u hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact False.elim <| sqAbsorb_right_succ_from_nfXADecorLeftPred_false hright hz
  ·
    rcases (show NFSqStableStepCtx (α := V) nfXADecorLeftPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xADecorLeftSPredTerm := by
      simpa [nfXADecorLeftPred] using hx.symm
    rcases plug_eq_xADecorLeftPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_sqStable_root_eq_xADecorLeftPred t u hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_sqStable_lhs_eq_x C' t u hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact False.elim <| sqStable_right_succ_from_nfXADecorLeftPred_false hright hz
  ·
    rcases (show NFDecorStepCtx (α := V) nfXADecorLeftPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xADecorLeftSPredTerm := by
      simpa [nfXADecorLeftPred] using hx.symm
    rcases plug_eq_xADecorLeftPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_decor_root_eq_xADecorLeftPred t u hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_decor_lhs_eq_x C' t u hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact decor_right_succ_from_nfXADecorLeftPred_eq_nfXA hright hz
  ·
    rcases (show NFC2C1StepCtx (α := V) nfXADecorLeftPred z from hstep) with
      ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xADecorLeftSPredTerm := by
      simpa [nfXADecorLeftPred] using hx.symm
    rcases plug_eq_xADecorLeftPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_c2c1_root_eq_xADecorLeftPred x0 p z0 hEq
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim <| no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft
    ·
      rcases hR with ⟨C', hC, hright⟩
      subst hC
      exact False.elim <| c2c1_right_succ_from_nfXADecorLeftPred_false hright hz

theorem plug_eq_uDecorLiftLeftPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uDecorLiftLeftSPredTerm) :
    (C = Ctx.hole ∧ r = uDecorLiftLeftSPredTerm) ∨
    (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xADecorLeftSPredTerm) ∨
    (∃ C', C = Ctx.right xADecorLeftSPredTerm C' ∧ Ctx.plug C' r = s) := by
  simpa [uDecorLiftLeftSPredTerm] using plug_eq_op_cases C r xADecorLeftSPredTerm s h

private theorem sqAbsorb_root_uDecorLiftLeftPred_forces_u_eq_x :
    RootMatchForces sqAbsorbPat uDecorLiftLeftSPredTerm
      (fun σ => σ 1 = x) := by
  intro σ hEq
  dsimp [sqAbsorbPat, Pat.inst, uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem sqAbsorb_root_uDecorLiftLeftPred_refute_of_u_eq_x :
    ∀ σ, σ 1 = x → Pat.inst σ sqAbsorbPat ≠ uDecorLiftLeftSPredTerm := by
  intro σ hux hEq
  dsimp [sqAbsorbPat, Pat.inst] at hEq
  rw [hux] at hEq
  dsimp [uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, s, x] at hEq
  injection hEq with hL hR
  injection hL with ht hu
  cases hu

def sqAbsorbRF_uDecorLiftLeftPred :
    SqAbsorbRightForcingWitness uDecorLiftLeftSPredTerm where
  Φ := fun σ => σ 1 = x
  forces := sqAbsorb_root_uDecorLiftLeftPred_forces_u_eq_x
  refute := sqAbsorb_root_uDecorLiftLeftPred_refute_of_u_eq_x

private theorem no_sqStable_root_uDecorLiftLeftPred :
    SqStableGlobalNoRootWitness uDecorLiftLeftSPredTerm := by
  intro σ hEq
  dsimp [sqStablePat, Pat.inst, uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, vTerm, s, x] at hEq
  nomatch hEq

private theorem decor_root_uDecorLiftLeftPred_forces_u_eq_x :
    RootMatchForces decorPat uDecorLiftLeftSPredTerm
      (fun σ => σ 1 = x) := by
  intro σ hEq
  dsimp [decorPat, Pat.inst, uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem decor_root_uDecorLiftLeftPred_refute_of_u_eq_x :
    ∀ σ, σ 1 = x → Pat.inst σ decorPat ≠ uDecorLiftLeftSPredTerm := by
  intro σ hux hEq
  dsimp [decorPat, Pat.inst] at hEq
  rw [hux] at hEq
  dsimp [uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, s, x] at hEq
  injection hEq with hL hR
  cases hR

def decorRF_uDecorLiftLeftPred :
    DecorRightForcingWitness uDecorLiftLeftSPredTerm where
  Φ := fun σ => σ 1 = x
  forces := decor_root_uDecorLiftLeftPred_forces_u_eq_x
  refute := decor_root_uDecorLiftLeftPred_refute_of_u_eq_x

private theorem no_c2c1_root_uDecorLiftLeftPred :
    C2C1LeftShellWitness uDecorLiftLeftSPredTerm := by
  intro σ hEq
  dsimp [c2c1Pat, Pat.inst, uDecorLiftLeftSPredTerm, xADecorLeftSPredTerm, vTerm, s, x] at hEq
  injection hEq with hL hR
  cases hL

theorem no_sqAbsorb_root_eq_uDecorLiftLeftPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uDecorLiftLeftSPredTerm := by
  exact no_sqAbsorb_root_eq_of_rightForcing sqAbsorbRF_uDecorLiftLeftPred t u

theorem no_sqStable_root_eq_uDecorLiftLeftPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uDecorLiftLeftSPredTerm := by
  exact no_sqStable_root_eq_of_globalNoRoot no_sqStable_root_uDecorLiftLeftPred t u

theorem no_decor_root_eq_uDecorLiftLeftPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uDecorLiftLeftSPredTerm := by
  exact no_decor_root_eq_of_rightForcing decorRF_uDecorLiftLeftPred t u

theorem no_c2c1_root_eq_uDecorLiftLeftPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uDecorLiftLeftSPredTerm := by
  exact no_c2c1_root_eq_of_leftShell no_c2c1_root_uDecorLiftLeftPred x0 p z0

private theorem eq_nfU_of_sqAbsorb_left_case_from_xADecorLeft {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' (((t.op u).op (u.op u))) = xADecorLeftSPredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFSqStepCtx (α := V) nfXADecorLeftPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXADecorLeftPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorLeftPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_sqStable_left_case_from_xADecorLeft {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((((t.op u).op (u.op u)).op u)) = xADecorLeftSPredTerm)
    (hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
  have hy : NFSqStableStepCtx (α := V) nfXADecorLeftPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXADecorLeftPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorLeftPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.SqStable, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_decor_left_case_from_xADecorLeft {z : NormalForm V}
    {C' : Ctx V} {t u : Term V}
    (hL : Ctx.plug C' ((t.op u).op (u.op (u.op u))) = xADecorLeftSPredTerm)
    (hz' : z.1 = (Ctx.plug C' (t.op u)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
  have hy : NFDecorStepCtx (α := V) nfXADecorLeftPred y := by
    refine ⟨C', t, u, ?_, rfl⟩
    simpa [nfXADecorLeftPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorLeftPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.Decor, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

private theorem eq_nfU_of_c2c1_left_case_from_xADecorLeft {z : NormalForm V}
    {C' : Ctx V} {x0 p z0 : Term V}
    (hL : Ctx.plug C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xADecorLeftSPredTerm)
    (hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) : z = nfU := by
  have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
    simpa [hz'] using z.2
  have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
    ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
  let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
  have hy : NFC2C1StepCtx (α := V) nfXADecorLeftPred y := by
    refine ⟨C', x0, p, z0, ?_, rfl⟩
    simpa [nfXADecorLeftPred] using hL.symm
  have hyEq : y = nfXA :=
    NFStepR_from_nfXADecorLeftPred_eq_nfXA
      (z := y) (by exact ⟨RuleId.C2C1, by simp [R4], hy⟩)
  have hyVal : y.1 = xATerm := by
    simpa [nfXA] using congrArg Subtype.val hyEq
  exact eq_nfU_of_left_val_sqRight hz' hyVal

theorem nfXADecorLeftPred_steps_to_nfXA :
    NFStepR (α := V) R4 nfXADecorLeftPred nfXA := by
  refine ⟨RuleId.Decor, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.right x (Ctx.left Ctx.hole s), x, x, ?_, ?_⟩
    ·
      change xADecorLeftSPredTerm
        = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole s))
            (((x.op x).op (x.op (x.op x))))
      simp [Ctx.plug, xADecorLeftSPredTerm, s, x]
    ·
      change xATerm = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole s)) (x.op x)
      simp [Ctx.plug, xATerm, A, s, x]

theorem NFStepR_from_nfUDecorLiftLeftSPred_eq_nfU {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorLiftLeftSPred z → z = nfU := by
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
    rcases (show NFSqStepCtx (α := V) nfUDecorLiftLeftSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uDecorLiftLeftSPredTerm := by
      simpa [nfUDecorLiftLeftSPred] using hx.symm
    rcases plug_eq_uDecorLiftLeftPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_sqAbsorb_root_eq_uDecorLiftLeftPred t u hEq
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_sqAbsorb_left_case_from_xADecorLeft hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' (((t.op u).op (u.op u))) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim <| no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs)
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim <| no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx)
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim <| no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases (show NFSqStableStepCtx (α := V) nfUDecorLiftLeftSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uDecorLiftLeftSPredTerm := by
      simpa [nfUDecorLiftLeftSPred] using hx.symm
    rcases plug_eq_uDecorLiftLeftPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_sqStable_root_eq_uDecorLiftLeftPred t u hEq
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_sqStable_left_case_from_xADecorLeft hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' ((((t.op u).op (u.op u)).op u)) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim <| no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs)
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim <| no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim <| no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases (show NFDecorStepCtx (α := V) nfUDecorLiftLeftSPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uDecorLiftLeftSPredTerm := by
      simpa [nfUDecorLiftLeftSPred] using hx.symm
    rcases plug_eq_uDecorLiftLeftPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_decor_root_eq_uDecorLiftLeftPred t u hEq
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_decor_left_case_from_xADecorLeft hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' ((t.op u).op (u.op (u.op u))) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim <| no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs)
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim <| no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim <| no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx)
  ·
    rcases (show NFC2C1StepCtx (α := V) nfUDecorLiftLeftSPred z from hstep) with
      ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uDecorLiftLeftSPredTerm := by
      simpa [nfUDecorLiftLeftSPred] using hx.symm
    rcases plug_eq_uDecorLiftLeftPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim <| no_c2c1_root_eq_uDecorLiftLeftPred x0 p z0 hEq
    ·
      rcases hL with ⟨C', hC, hL⟩
      subst hC
      have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
        simpa [Ctx.plug] using hz
      exact eq_nfU_of_c2c1_left_case_from_xADecorLeft hL hz'
    ·
      rcases hR with ⟨C', hC, hS⟩
      subst hC
      rcases plug_eq_s_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hS with h0 | h1 | h2
      ·
        rcases h0 with ⟨rfl, hs⟩
        exact False.elim <| no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs)
      ·
        rcases h1 with ⟨_, hx⟩
        exact False.elim <| no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
      ·
        rcases h2 with ⟨_, hx⟩
        exact False.elim <| no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)

/-!
## Root-behavior cells in registry order

This section is the registry-facing view of the root behavior table.
Proofs above remain in their dependency-friendly places; here we expose the
filled `(rule,target)` cells in the same order as `ProofCore_R4Registry`.
-/


theorem no_sqAbsorb_root_xADecorAPred :
    NoRootInstance sqAbsorbPat xADecorAPredTerm := by
  simpa [xADecorAPredTerm] using
    (no_sqAbsorb_root_x_left (q := A.op (s.op A)))

theorem no_sqStable_root_xADecorAPred :
    NoRootInstance sqStablePat xADecorAPredTerm := by
  simpa [xADecorAPredTerm] using
    (no_sqStable_root_x_left (q := A.op (s.op A)))

theorem no_decor_root_xADecorAPred :
    NoRootInstance decorPat xADecorAPredTerm := by
  simpa [xADecorAPredTerm] using
    (no_decor_root_x_left (q := A.op (s.op A)))

theorem no_c2c1_root_xADecorAPred :
    NoRootInstance c2c1Pat xADecorAPredTerm := by
  simpa [xADecorAPredTerm] using
    (no_c2c1_root_x_left (q := A.op (s.op A)))

theorem no_sqAbsorb_root_eq_xADecorAPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xADecorAPredTerm := by
  exact no_sqAbsorb_root_eq_of_no_instance no_sqAbsorb_root_xADecorAPred t u

theorem no_sqStable_root_eq_xADecorAPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xADecorAPredTerm := by
  exact no_sqStable_root_eq_of_no_instance no_sqStable_root_xADecorAPred t u

theorem no_decor_root_eq_xADecorAPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xADecorAPredTerm := by
  exact no_decor_root_eq_of_no_instance no_decor_root_xADecorAPred t u

theorem no_c2c1_root_eq_xADecorAPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xADecorAPredTerm := by
  exact no_c2c1_root_eq_of_no_instance no_c2c1_root_xADecorAPred x0 p z0


end KernelDecor

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
