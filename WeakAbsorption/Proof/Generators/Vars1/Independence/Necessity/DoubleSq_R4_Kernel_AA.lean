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

section KernelAA

def nfXASqAPred : NormalForm V :=
  ⟨xASqAPredTerm, xASqAPred_normal⟩

private theorem xASqLeftSPred_not_normal :
    ¬ Normal (α := V) xASqLeftSPredTerm := by
  intro hN
  have hR : Normal (α := V) (A.op s) :=
    ((Normal_op_iff (α := V) x (A.op s)).1 hN).2.1
  have hnoC1 : ¬ IsC1Root (α := V) A s :=
    ((Normal_op_iff (α := V) A s).1 hR).2.2.1
  apply hnoC1
  refine ⟨s, ?_⟩
  dsimp [A, s, x]

private theorem eq_nfXASqRight_of_right_val {z : NormalForm V} {w : Term V}
    (hz' : z.1 = x.op (w.op A))
    (hw : w = s) : z = nfXASqRightPred := by
  apply Subtype.ext
  rw [hw] at hz'
  simpa [nfXASqRightPred, xASqRightSPredTerm, A, s, x] using hz'

theorem plug_eq_AA_rhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = A.op A) :
    (C = Ctx.hole ∧ r = A.op A) ∨
    (∃ C', C = Ctx.left C' A ∧ Ctx.plug C' r = A) ∨
    (∃ C', C = Ctx.right A C' ∧ Ctx.plug C' r = A) := by
  cases C with
  | hole =>
      exact Or.inl ⟨rfl, by simpa [Ctx.plug] using h⟩
  | left C r0 =>
      dsimp [Ctx.plug, A] at h
      injection h with hL hR
      subst hR
      exact Or.inr <| Or.inl ⟨C, rfl, by simpa using hL⟩
  | right l C =>
      dsimp [Ctx.plug, A] at h
      injection h with hL hR
      subst hL
      exact Or.inr <| Or.inr ⟨C, rfl, by simpa using hR⟩

theorem plug_eq_xASqAPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = xASqAPredTerm) :
    (C = Ctx.hole ∧ r = xASqAPredTerm) ∨
    (∃ C', C = Ctx.left C' (A.op A) ∧ Ctx.plug C' r = x) ∨
    (∃ C', C = Ctx.right x C' ∧ Ctx.plug C' r = A.op A) := by
  simpa [xASqAPredTerm] using plug_eq_op_cases C r x (A.op A) h

private theorem no_sqAbsorb_root_xASqAPred :
    NoRootInstance sqAbsorbPat xASqAPredTerm := by
  simpa [xASqAPredTerm] using
    (no_sqAbsorb_root_x_left (q := A.op A))

private theorem no_sqStable_root_xASqAPred :
    NoRootInstance sqStablePat xASqAPredTerm := by
  simpa [xASqAPredTerm] using
    (no_sqStable_root_x_left (q := A.op A))

private theorem no_decor_root_xASqAPred :
    NoRootInstance decorPat xASqAPredTerm := by
  simpa [xASqAPredTerm] using
    (no_decor_root_x_left (q := A.op A))

private theorem no_c2c1_root_xASqAPred :
    NoRootInstance c2c1Pat xASqAPredTerm := by
  simpa [xASqAPredTerm] using
    (no_c2c1_root_x_left (q := A.op A))


theorem no_sqAbsorb_root_eq_xASqAPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ xASqAPredTerm := by
  exact no_sqAbsorb_root_eq_of_no_instance no_sqAbsorb_root_xASqAPred t u

theorem no_sqStable_root_eq_xASqAPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ xASqAPredTerm := by
  exact no_sqStable_root_eq_of_no_instance no_sqStable_root_xASqAPred t u

theorem no_decor_root_eq_xASqAPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ xASqAPredTerm := by
  exact no_decor_root_eq_of_no_instance no_decor_root_xASqAPred t u

theorem no_c2c1_root_eq_xASqAPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ xASqAPredTerm := by
  exact no_c2c1_root_eq_of_no_instance no_c2c1_root_xASqAPred x0 p z0

--

theorem no_sqStable_root_eq_AA
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ A.op A := by
  intro hEq
  dsimp [A, s, x] at hEq
  nomatch hEq

theorem no_decor_root_eq_AA
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ A.op A := by
  intro hEq
  dsimp [A, s, x] at hEq
  nomatch hEq

theorem no_c2c1_root_eq_AA
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ A.op A := by
  intro hEq
  dsimp [A, s, x] at hEq
  nomatch hEq



theorem NFStepR_from_nfXASqAPred_cases {z : NormalForm V} :
    NFStepR (α := V) R4 nfXASqAPred z →
      z = nfXA ∨ z = nfXASqRightPred := by
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
    rcases (show NFSqStepCtx (α := V) nfXASqAPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = xASqAPredTerm := by
      simpa [nfXASqAPred] using hx.symm
    rcases plug_eq_xASqAPred_lhs_cases C (((t.op u).op (u.op u))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqAbsorb_root_eq_xASqAPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_sqAbsorb_lhs_eq_x C' t u hleft)
    ·
      rcases hR with ⟨C', hC, hAA⟩
      subst hC
      rcases plug_eq_AA_rhs_cases C' (((t.op u).op (u.op u))) hAA with hAA0 | hAA1 | hAA2
      ·
        rcases hAA0 with ⟨rfl, hEq⟩
        have htuA : t.op u = A := by
          dsimp [A] at hEq
          injection hEq with hL hR
        have hz' : z.1 = x.op (t.op u) := by
          simpa [Ctx.plug, x] using hz
        exact Or.inl (eq_nfXA_of_right_val hz' htuA)
      ·
        rcases hAA1 with ⟨C'', hC'', hAeq⟩
        subst hC''
        rcases plug_eq_A_cases C'' (((t.op u).op (u.op u))) hAeq with
          hA0 | hA1 | hA2 | hA3 | hA4 | hA5 | hA6
        ·
          rcases hA0 with ⟨rfl, hEq⟩
          have htu : t.op u = s := sqAbsorb_root_eq_A_forces_tu_eq_s hEq
          have hz' : z.1 = x.op ((t.op u).op A) := by
            simpa [Ctx.plug, x] using hz
          exact Or.inr (eq_nfXASqRight_of_right_val hz' htu)
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
        rcases hAA2 with ⟨C'', hC'', hAeq⟩
        subst hC''
        rcases plug_eq_A_cases C'' (((t.op u).op (u.op u))) hAeq with
          hA0 | hA1 | hA2 | hA3 | hA4 | hA5 | hA6
        ·
          rcases hA0 with ⟨rfl, hEq⟩
          have htu : t.op u = s := sqAbsorb_root_eq_A_forces_tu_eq_s hEq
          have hz' : z.1 = x.op (A.op (t.op u)) := by
            simpa [Ctx.plug, x] using hz
          have hzN : Normal (α := V) (x.op (A.op (t.op u))) := by
            simpa [hz'] using z.2
          rw [htu] at hzN
          exact False.elim (xASqLeftSPred_not_normal hzN)
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
    rcases (show NFSqStableStepCtx (α := V) nfXASqAPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xASqAPredTerm := by
      simpa [nfXASqAPred] using hx.symm
    rcases plug_eq_xASqAPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqStable_root_eq_xASqAPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_sqStable_lhs_eq_x C' t u hleft)
    ·
      rcases hR with ⟨C', hC, hAA⟩
      subst hC
      rcases plug_eq_AA_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hAA with hAA0 | hAA1 | hAA2
      ·
        rcases hAA0 with ⟨rfl, hEq⟩
        exact False.elim (no_sqStable_root_eq_AA t u hEq)
      ·
        rcases hAA1 with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_sqStable_lhs_eq_A C'' t u hAeq)
      ·
        rcases hAA2 with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_sqStable_lhs_eq_A C'' t u hAeq)
  ·
    rcases (show NFDecorStepCtx (α := V) nfXASqAPred z from hstep) with
      ⟨C, t, u, hx, hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xASqAPredTerm := by
      simpa [nfXASqAPred] using hx.symm
    rcases plug_eq_xASqAPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_decor_root_eq_xASqAPred t u hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_decor_lhs_eq_x C' t u hleft)
    ·
      rcases hR with ⟨C', hC, hAA⟩
      subst hC
      rcases plug_eq_AA_rhs_cases C' ((t.op u).op (u.op (u.op u))) hAA with hAA0 | hAA1 | hAA2
      ·
        rcases hAA0 with ⟨rfl, hEq⟩
        exact False.elim (no_decor_root_eq_AA t u hEq)
      ·
        rcases hAA1 with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_decor_lhs_eq_A C'' t u hAeq)
      ·
        rcases hAA2 with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_decor_lhs_eq_A C'' t u hAeq)
  ·
    rcases (show NFC2C1StepCtx (α := V) nfXASqAPred z from hstep) with
      ⟨C, x0, p, z0, hx, hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xASqAPredTerm := by
      simpa [nfXASqAPred] using hx.symm
    rcases plug_eq_xASqAPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
      h0 | hL | hR
    ·
      rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_c2c1_root_eq_xASqAPred x0 p z0 hEq)
    ·
      rcases hL with ⟨C', hC, hleft⟩
      subst hC
      exact False.elim (no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft)
    ·
      rcases hR with ⟨C', hC, hAA⟩
      subst hC
      rcases plug_eq_AA_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hAA with hAA0 | hAA1 | hAA2
      ·
        rcases hAA0 with ⟨rfl, hEq⟩
        exact False.elim (no_c2c1_root_eq_AA x0 p z0 hEq)
      ·
        rcases hAA1 with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_c2c1_lhs_eq_A C'' x0 p z0 hAeq)
      ·
        rcases hAA2 with ⟨C'', hC'', hAeq⟩
        subst hC''
        exact False.elim (no_plug_c2c1_lhs_eq_A C'' x0 p z0 hAeq)

theorem plug_eq_uSqLiftAPred_lhs_cases
    (C : Ctx V) (r : Term V)
    (h : Ctx.plug C r = uSqLiftAPredTerm) :
    (C = Ctx.hole ∧ r = uSqLiftAPredTerm) ∨
    (∃ C', C = Ctx.left C' s ∧ Ctx.plug C' r = xASqAPredTerm) ∨
    (∃ C', C = Ctx.right xASqAPredTerm C' ∧ Ctx.plug C' r = s) := by
  simpa [uSqLiftAPredTerm] using plug_eq_op_cases C r xASqAPredTerm s h

private theorem eq_nfUSqLiftRight_of_left_val {z : NormalForm V} {w : Term V}
    (hz' : z.1 = w.op s)
    (hw : w = xASqRightSPredTerm) : z = nfUSqLiftRightSPred := by
  apply Subtype.ext
  rw [hw] at hz'
  simpa [nfUSqLiftRightSPred, uSqLiftRightSPredTerm] using hz'

----------------------------------------------------------
private theorem sqAbsorb_root_uSqLiftAPred_forces_u_eq_x :
    RootMatchForces sqAbsorbPat uSqLiftAPredTerm
      (fun σ => σ 1 = x) := by
  intro σ hEq
  dsimp [sqAbsorbPat, Pat.inst, uSqLiftAPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hR

private theorem sqAbsorb_root_uSqLiftAPred_refute_of_u_eq_x :
    ∀ σ, σ 1 = x → Pat.inst σ sqAbsorbPat ≠ uSqLiftAPredTerm := by
  intro σ hux hEq
  dsimp [sqAbsorbPat, Pat.inst] at hEq
  rw [hux] at hEq
  dsimp [uSqLiftAPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hL with ht hu
  cases hu

def sqAbsorbRF_uSqLiftAPred :
    SqAbsorbRightForcingWitness uSqLiftAPredTerm where
  Φ := fun σ => σ 1 = x
  forces := sqAbsorb_root_uSqLiftAPred_forces_u_eq_x
  refute := sqAbsorb_root_uSqLiftAPred_refute_of_u_eq_x

theorem no_sqAbsorb_root_eq_uSqLiftAPred
    (t u : Term V) :
    ((t.op u).op (u.op u)) ≠ uSqLiftAPredTerm := by
  exact no_sqAbsorb_root_eq_of_rightForcing sqAbsorbRF_uSqLiftAPred t u

----------------------------------------------------------

private theorem no_sqStable_root_uSqLiftAPred :
    SqStableGlobalNoRootWitness uSqLiftAPredTerm := by
  intro σ hEq
  dsimp [sqStablePat, Pat.inst, uSqLiftAPredTerm, xASqAPredTerm, A, s, x] at hEq
  nomatch hEq

theorem no_sqStable_root_eq_uSqLiftAPred
    (t u : Term V) :
    (((t.op u).op (u.op u)).op u) ≠ uSqLiftAPredTerm := by
  exact no_sqStable_root_eq_of_globalNoRoot no_sqStable_root_uSqLiftAPred t u

theorem no_decor_root_uSqLiftAPred :
    DecorRightShellWitness uSqLiftAPredTerm := by
  intro σ hEq
  dsimp [decorPat, Pat.inst, uSqLiftAPredTerm, xASqAPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  injection hR with hu1 hu2
  cases hu2

theorem no_decor_root_eq_uSqLiftAPred
    (t u : Term V) :
    ((t.op u).op (u.op (u.op u))) ≠ uSqLiftAPredTerm := by
  exact no_decor_root_eq_of_rightShell no_decor_root_uSqLiftAPred t u

theorem no_c2c1_root_uSqLiftAPred :
    C2C1LeftShellWitness uSqLiftAPredTerm := by
  intro σ hEq
  dsimp [c2c1Pat, Pat.inst, uSqLiftAPredTerm, xASqAPredTerm, A, s, x] at hEq
  injection hEq with hL hR
  cases hL

theorem no_c2c1_root_eq_uSqLiftAPred
    (x0 p z0 : Term V) :
    (((x0.op (p.op z0)).op z0).op (p.op z0)) ≠ uSqLiftAPredTerm := by
  exact no_c2c1_root_eq_of_leftShell no_c2c1_root_uSqLiftAPred x0 p z0

private theorem finish_from_nfXASqAPred {y z : NormalForm V}
    (hy : NFStepR (α := V) R4 nfXASqAPred y)
    (hz : z.1 = y.1.op s) :
    z = nfU ∨ z = nfUSqLiftRightSPred := by
  rcases NFStepR_from_nfXASqAPred_cases (z := y) hy with hyXA | hyR
  ·
    have hyVal : y.1 = xATerm := by
      simpa [nfXA] using congrArg Subtype.val hyXA
    exact Or.inl (eq_nfU_of_left_val_sqRight hz hyVal)
  ·
    have hyVal : y.1 = xASqRightSPredTerm := by
      simpa [nfXASqRightPred] using congrArg Subtype.val hyR
    exact Or.inr (eq_nfUSqLiftRight_of_left_val hz hyVal)

theorem NFStepR_from_nfUSqLiftAPred_cases {z : NormalForm V} :
    NFStepR (α := V) R4 nfUSqLiftAPred z →
      z = nfU ∨ z = nfUSqLiftRightSPred := by
  intro h; rcases h with ⟨tag, htag, hstep⟩
  have htag' :
      tag = RuleId.SqAbsorb ∨ tag = RuleId.SqStable ∨ tag = RuleId.Decor ∨ tag = RuleId.C2C1 := by
    simpa [R4] using htag
  rcases htag' with rfl | rfl | rfl | rfl
  ·
    rcases (show NFSqStepCtx (α := V) nfUSqLiftAPred z from hstep) with ⟨C,t,u,hx,hz⟩
    have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uSqLiftAPredTerm := by simpa [nfUSqLiftAPred] using hx.symm
    rcases plug_eq_uSqLiftAPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
    · rcases h0 with ⟨rfl,hEq⟩; exact False.elim (no_sqAbsorb_root_eq_uSqLiftAPred t u hEq)
    · rcases hL with ⟨C',hC,hL⟩
      subst hC
      let y : NormalForm V := ⟨Ctx.plug C' (t.op u),
        ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 (by simpa [hz] using z.2)).1⟩
      have hy : NFStepR (α := V) R4 nfXASqAPred y := by
        exact ⟨RuleId.SqAbsorb, by simp [R4], by
          refine ⟨C', t, u, ?_, rfl⟩
          simpa [nfXASqAPred] using hL.symm⟩
      have hz' : z.1 = y.1.op s := by
        simpa [y, Ctx.plug]
      exact finish_from_nfXASqAPred hy hz'

    · rcases hR with ⟨C',rfl,hS⟩; rcases plug_eq_s_cases C' (((t.op u).op (u.op u))) hS with h0 | h1 | h2
      · rcases h0 with ⟨rfl,hs⟩; exact False.elim (no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs))
      · rcases h1 with ⟨_,hx⟩; exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
      · rcases h2 with ⟨_,hx⟩; exact False.elim (no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx))
  ·
    rcases (show NFSqStableStepCtx (α := V) nfUSqLiftAPred z from hstep) with ⟨C,t,u,hx,hz⟩
    have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uSqLiftAPredTerm := by simpa [nfUSqLiftAPred] using hx.symm
    rcases plug_eq_uSqLiftAPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
    · rcases h0 with ⟨rfl,hEq⟩; exact False.elim (no_sqStable_root_eq_uSqLiftAPred t u hEq)
    · rcases hL with ⟨C',hC,hL⟩ -- rfl から hC に変更
      subst hC -- 明示的に subst
      let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)),
        ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 (by simpa [hz] using z.2)).1⟩
      have hy : NFStepR (α := V) R4 nfXASqAPred y := by
        exact ⟨RuleId.SqStable, by simp [R4], by
          refine ⟨C', t, u, ?_, rfl⟩
          simpa [nfXASqAPred] using hL.symm⟩
      exact finish_from_nfXASqAPred hy (by simpa [y, Ctx.plug] using hz)
    · rcases hR with ⟨C',rfl,hS⟩; rcases plug_eq_s_cases C' ((((t.op u).op (u.op u)).op u)) hS with h0 | h1 | h2
      · rcases h0 with ⟨rfl,hs⟩; exact False.elim (no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs))
      · rcases h1 with ⟨_,hx⟩; exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
      · rcases h2 with ⟨_,hx⟩; exact False.elim (no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx))
  ·
    rcases (show NFDecorStepCtx (α := V) nfUSqLiftAPred z from hstep) with ⟨C,t,u,hx,hz⟩
    have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uSqLiftAPredTerm := by simpa [nfUSqLiftAPred] using hx.symm
    rcases plug_eq_uSqLiftAPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
    · rcases h0 with ⟨rfl,hEq⟩; exact False.elim (no_decor_root_eq_uSqLiftAPred t u hEq)
    · rcases hL with ⟨C',hC,hL⟩ -- rfl から hC に変更
      subst hC -- 明示的に subst
      let y : NormalForm V := ⟨Ctx.plug C' (t.op u),
        ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 (by simpa [hz] using z.2)).1⟩
      have hy : NFStepR (α := V) R4 nfXASqAPred y := by
        exact ⟨RuleId.Decor, by simp [R4], by
          refine ⟨C', t, u, ?_, rfl⟩
          simpa [nfXASqAPred] using hL.symm⟩
      exact finish_from_nfXASqAPred hy (by simpa [y, Ctx.plug] using hz)
    · rcases hR with ⟨C',rfl,hS⟩; rcases plug_eq_s_cases C' ((t.op u).op (u.op (u.op u))) hS with h0 | h1 | h2
      · rcases h0 with ⟨rfl,hs⟩; exact False.elim (no_plug_decor_lhs_eq_s Ctx.hole t u (by simpa using hs))
      · rcases h1 with ⟨_,hx⟩; exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
      · rcases h2 with ⟨_,hx⟩; exact False.elim (no_plug_decor_lhs_eq_x Ctx.hole t u (by simpa using hx))
  ·
    rcases (show NFC2C1StepCtx (α := V) nfUSqLiftAPred z from hstep) with ⟨C,x0,p,z0,hx,hz⟩
    have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uSqLiftAPredTerm := by simpa [nfUSqLiftAPred] using hx.symm
    rcases plug_eq_uSqLiftAPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
    · rcases h0 with ⟨rfl,hEq⟩; exact False.elim (no_c2c1_root_eq_uSqLiftAPred x0 p z0 hEq)
    · rcases hL with ⟨C',hC,hL⟩ -- rfl から hC に変更
      subst hC -- 明示的に subst
      let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0),
        ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 (by simpa [hz] using z.2)).1⟩
      have hy : NFStepR (α := V) R4 nfXASqAPred y := by
        exact ⟨RuleId.C2C1, by simp [R4], by
          refine ⟨C', x0, p, z0, ?_, rfl⟩
          simpa [nfXASqAPred] using hL.symm⟩
      exact finish_from_nfXASqAPred hy (by simpa [y, Ctx.plug] using hz)
    · rcases hR with ⟨C',rfl,hS⟩; rcases plug_eq_s_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hS with h0 | h1 | h2
      · rcases h0 with ⟨rfl,hs⟩; exact False.elim (no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs))
      · rcases h1 with ⟨_,hx⟩; exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))
      · rcases h2 with ⟨_,hx⟩; exact False.elim (no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx))


private theorem nfXASqAPred_sqAbsorb_to_nfXA :
    NFSqStepCtx (α := V) nfXASqAPred nfXA := by
  refine ⟨Ctx.right x Ctx.hole, s, s, ?_, ?_⟩
  ·
    change xASqAPredTerm = Ctx.plug (Ctx.right x Ctx.hole) (((s.op s).op (s.op s)))
    simp [Ctx.plug, xASqAPredTerm, A, s, x]
  ·
    change xATerm = Ctx.plug (Ctx.right x Ctx.hole) (s.op s)
    simp [Ctx.plug, xATerm, A, s, x]

private theorem nfXASqAPred_sqAbsorb_to_nfXASqRightPred :
    NFSqStepCtx (α := V) nfXASqAPred nfXASqRightPred := by
  refine ⟨Ctx.right x (Ctx.left Ctx.hole A), x, x, ?_, ?_⟩
  ·
    change xASqAPredTerm = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole A)) (((x.op x).op (x.op x)))
    simp [Ctx.plug, xASqAPredTerm, A, s, x]
  ·
    change xASqRightSPredTerm = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole A)) (x.op x)
    simp [Ctx.plug, xASqRightSPredTerm, A, s, x]

private theorem nfUSqLiftAPred_sqAbsorb_to_nfU :
    NFSqStepCtx (α := V) nfUSqLiftAPred nfU := by
  refine ⟨Ctx.left (Ctx.right x Ctx.hole) s, s, s, ?_, ?_⟩
  ·
    change uSqLiftAPredTerm
      = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s) (((s.op s).op (s.op s)))
    simp [Ctx.plug, uSqLiftAPredTerm, xASqAPredTerm, A, s, x]
  ·
    change uTerm = Ctx.plug (Ctx.left (Ctx.right x Ctx.hole) s) (s.op s)
    simp [Ctx.plug, uTerm, A, s, x]

private theorem nfUSqLiftAPred_sqAbsorb_to_nfUSqLiftRightSPred :
    NFSqStepCtx (α := V) nfUSqLiftAPred nfUSqLiftRightSPred := by
  refine ⟨Ctx.left (Ctx.right x (Ctx.left Ctx.hole A)) s, x, x, ?_, ?_⟩
  ·
    change uSqLiftAPredTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole A)) s)
          (((x.op x).op (x.op x)))
    simp [Ctx.plug, uSqLiftAPredTerm, xASqAPredTerm, A, s, x]
  ·
    change uSqLiftRightSPredTerm
      = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole A)) s) (x.op x)
    simp [Ctx.plug, uSqLiftRightSPredTerm, xASqRightSPredTerm, A, s, x]



theorem ctxProfileCert_nfXASqAPred_sqAbsorb :
    CtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFSqStepCtx (α := V) src z)
      nfXASqAPred
      ctxProfile_nfXASqAPred_sqAbsorb := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [ctxProfile_nfXASqAPred_sqAbsorb] at he
    rcases he with rfl | rfl
    · exact nfXASqAPred_sqAbsorb_to_nfXA
    · exact nfXASqAPred_sqAbsorb_to_nfXASqRightPred
  · intro z hz
    have hstep : NFStepR (α := V) R4 nfXASqAPred z :=
      ⟨RuleId.SqAbsorb, by simp [R4], hz⟩
    rcases NFStepR_from_nfXASqAPred_cases (z := z) hstep with h | h
    · refine ⟨(.right, .nfXA), by simp [ctxProfile_nfXASqAPred_sqAbsorb], ?_⟩
      simpa [ctxNFOfTag] using h
    · refine ⟨(.right, .nfXASqRightPred), by simp [ctxProfile_nfXASqAPred_sqAbsorb], ?_⟩
      simpa [ctxNFOfTag] using h

def ctxProfile_nfUSqLiftAPred_sqAbsorb : CtxProfile :=
  [(.left, .nfU), (.left, .nfUSqLiftRightPred)]

theorem ctxProfileCert_nfUSqLiftAPred_sqAbsorb :
    CtxCellProfileCertificate
      ctxNFOfTag
      (fun src z => NFSqStepCtx (α := V) src z)
      nfUSqLiftAPred
      ctxProfile_nfUSqLiftAPred_sqAbsorb := by
  refine ⟨?_, ?_⟩
  · intro e he
    simp [ctxProfile_nfUSqLiftAPred_sqAbsorb] at he
    rcases he with rfl | rfl
    · exact nfUSqLiftAPred_sqAbsorb_to_nfU
    · exact nfUSqLiftAPred_sqAbsorb_to_nfUSqLiftRightSPred
  · intro z hz
    have hstep : NFStepR (α := V) R4 nfUSqLiftAPred z :=
      ⟨RuleId.SqAbsorb, by simp [R4], hz⟩
    rcases NFStepR_from_nfUSqLiftAPred_cases (z := z) hstep with h | h
    · refine ⟨(.left, .nfU), by simp [ctxProfile_nfUSqLiftAPred_sqAbsorb], ?_⟩
      simpa [ctxNFOfTag] using h
    · refine ⟨(.left, .nfUSqLiftRightPred), by simp [ctxProfile_nfUSqLiftAPred_sqAbsorb], ?_⟩
      simpa [ctxNFOfTag] using h





end KernelAA

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
