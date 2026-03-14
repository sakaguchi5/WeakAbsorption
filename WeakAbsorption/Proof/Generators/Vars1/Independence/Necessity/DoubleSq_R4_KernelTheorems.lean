import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Core
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Kernel_SA
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Kernel_AA
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Kernel_Decor
import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Kernel_StableHoleBridge

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

section CoreKernelTheorems

open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Spec
open WAA

theorem saKernel_exact_support_theorem :
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfXASqRightPred z → z = nfXA) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfXASqRightPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFDecorStepCtx (α := V) nfXASqRightPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfXASqRightPred z) ∧
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUSqLiftRightSPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUSqLiftRightSPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFDecorStepCtx (α := V) nfUSqLiftRightSPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUSqLiftRightSPred z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sqAbsorb_succ_from_nfXASqRightPred_eq_nfXA (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfXASqRightPred (z := z) hz
  · intro z hz
    exact no_decor_succ_from_nfXASqRightPred (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfXASqRightPred (z := z) hz
  · intro z hz
    exact sqAbsorb_succ_from_nfUSqLiftRightSPred_eq_nfU (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUSqLiftRightSPred (z := z) hz
  · intro z hz
    exact no_decor_succ_from_nfUSqLiftRightSPred (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUSqLiftRightSPred (z := z) hz

theorem no_sqAbsorb_succ_from_nfUStablePred {z : NormalForm V} :
    ¬ NFSqStepCtx (α := V) nfUStablePred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uStablePredTerm := by
    simpa [nfUStablePred] using hx.symm
  rcases plug_eq_uStablePred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqAbsorb_root_eq_uStablePred hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFSqStepCtx (α := V) nfXAStablePred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXAStablePred] using hleft.symm
    have hyAlt : y.1 = xAStableAltTerm :=
      sqAbsorb_succ_from_nfXAStablePred_alt (z := y) hy
    have : Normal (α := V) xAStableAltTerm := by
      simpa [hyAlt] using y.2
    exact xAStableAlt_not_normal this
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    exact no_plug_sqAbsorb_lhs_eq_s C' t u hS

theorem no_decor_succ_from_nfUStablePred {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfUStablePred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uStablePredTerm := by
    simpa [nfUStablePred] using hx.symm
  rcases plug_eq_uStablePred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_decor_root_eq_uStablePred hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFDecorStepCtx (α := V) nfXAStablePred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXAStablePred] using hleft.symm
    exact no_decor_succ_from_nfXAStablePred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    exact no_plug_decor_lhs_eq_s C' t u hS

theorem no_c2c1_succ_from_nfUStablePred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfUStablePred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uStablePredTerm := by
    simpa [nfUStablePred] using hx.symm
  rcases plug_eq_uStablePred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    dsimp [uStablePredTerm, xAStablePredTerm, A, s, x] at hEq
    nomatch hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
    have hy : NFC2C1StepCtx (α := V) nfXAStablePred y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfXAStablePred] using hleft.symm
    exact no_c2c1_succ_from_nfXAStablePred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    exact no_plug_c2c1_lhs_eq_s C' x0 p z0 hS

theorem stableKernel_exact_support_theorem :
    (∀ {z : NormalForm V}, ¬ NFSqStepCtx (α := V) nfUStablePred z) ∧
    (∀ {z : NormalForm V}, NFSqStableStepCtx (α := V) nfUStablePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFDecorStepCtx (α := V) nfUStablePred z) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUStablePred z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact no_sqAbsorb_succ_from_nfUStablePred (z := z) hz
  · intro z hz
    exact sqStable_step_from_nfUStablePred_eq_nfU (z := z) hz
  · intro z hz
    exact no_decor_succ_from_nfUStablePred (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUStablePred (z := z) hz

theorem stableKernel_rulewise_codomain_theorem :
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUStablePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFSqStableStepCtx (α := V) nfUStablePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUStablePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFC2C1StepCtx (α := V) nfUStablePred z → z = nfU) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact False.elim (no_sqAbsorb_succ_from_nfUStablePred (z := z) hz)
  · intro z hz
    exact sqStable_step_from_nfUStablePred_eq_nfU (z := z) hz
  · intro z hz
    exact False.elim (no_decor_succ_from_nfUStablePred (z := z) hz)
  · intro z hz
    exact False.elim (no_c2c1_succ_from_nfUStablePred (z := z) hz)

theorem stableKernel_codomain_theorem :
    NFStepR (α := V) R4 nfUStablePred nfU ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUStablePred z → z = nfU) := by
  refine ⟨nfUStablePred_steps_to_nfU, ?_⟩
  intro z hz
  exact NFStepR_from_nfUStablePred_eq_nfU (z := z) hz

theorem stableKernel_semantic_theorem :
    coreKernelRegime .stableKernel = .pure ∧
    coreKernelCodomainStatus .stableKernel = .settled ∧
    coreKernelSupportStatus .stableKernel = .exact := by
  decide

theorem holeKernel_exact_support_theorem :
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUHolePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUHolePred z) ∧
    (∀ {z : NormalForm V}, ¬ NFDecorStepCtx (α := V) nfUHolePred z) ∧
    (∀ {z : NormalForm V}, NFC2C1StepCtx (α := V) nfUHolePred z → z = nfU) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sqAbsorb_succ_from_nfUHolePred_eq_nfU (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUHolePred (z := z) hz
  · intro z hz
    exact no_decor_succ_from_nfUHolePred (z := z) hz
  · intro z hz
    exact c2c1_succ_from_nfUHolePred_eq_nfU (z := z) hz

theorem holeKernel_semantic_theorem :
    coreKernelRegime .holeKernel = .pure ∧
    coreKernelCodomainStatus .holeKernel = .settled ∧
    coreKernelSupportStatus .holeKernel = .exact := by
  decide

theorem decorHoleKernel_exact_support_theorem :
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUDecorHolePred z → z = nfUHolePred) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUDecorHolePred z) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorHolePred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUDecorHolePred z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sqAbsorb_succ_from_nfUDecorHolePred_eq_nfUHolePred (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUDecorHolePred (z := z) hz
  · intro z hz
    exact decor_succ_from_nfUDecorHolePred_eq_nfU (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUDecorHolePred (z := z) hz

theorem decorHoleKernel_semantic_theorem :
    coreKernelRegime .decorHoleKernel = .pure ∧
    coreKernelCodomainStatus .decorHoleKernel = .settled ∧
    coreKernelSupportStatus .decorHoleKernel = .exact := by
  decide

theorem no_sqAbsorb_succ_from_nfXADecorRightPred {z : NormalForm V} :
    ¬ NFSqStepCtx (α := V) nfXADecorRightPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = xADecorRightSPredTerm := by
    simpa [nfXADecorRightPred] using hx.symm
  rcases plug_eq_xADecorRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqAbsorb_root_eq_xADecorRightPred t u hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_sqAbsorb_lhs_eq_x C' t u hleft
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact sqAbsorb_right_succ_from_nfXADecorRightPred_false hright hz

theorem no_sqStable_succ_from_nfXADecorRightPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfXADecorRightPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xADecorRightSPredTerm := by
    simpa [nfXADecorRightPred] using hx.symm
  rcases plug_eq_xADecorRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_xADecorRightPred t u hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_sqStable_lhs_eq_x C' t u hleft
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact sqStable_right_succ_from_nfXADecorRightPred_false hright hz

theorem decor_step_from_nfXADecorRightPred_eq_nfXA {z : NormalForm V} :
    NFDecorStepCtx (α := V) nfXADecorRightPred z → z = nfXA := by
  intro hz
  exact NFStepR_from_nfXADecorRightPred_eq_nfXA (z := z)
    ⟨RuleId.Decor, by simp [R4], hz⟩

theorem no_c2c1_succ_from_nfXADecorRightPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfXADecorRightPred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xADecorRightSPredTerm := by
    simpa [nfXADecorRightPred] using hx.symm
  rcases plug_eq_xADecorRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_xADecorRightPred x0 p z0 hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact c2c1_right_succ_from_nfXADecorRightPred_false hright hz

theorem no_sqAbsorb_succ_from_nfUDecorLiftRightSPred {z : NormalForm V} :
    ¬ NFSqStepCtx (α := V) nfUDecorLiftRightSPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uDecorLiftRightSPredTerm := by
    simpa [nfUDecorLiftRightSPred] using hx.symm
  rcases plug_eq_uDecorLiftRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqAbsorb_root_eq_uDecorLiftRightPred t u hEq
  · rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFSqStepCtx (α := V) nfXADecorRightPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXADecorRightPred] using hL.symm
    exact no_sqAbsorb_succ_from_nfXADecorRightPred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' (((t.op u).op (u.op u))) hS with h0 | h1 | h2
    · rcases h0 with ⟨rfl, hs⟩
      exact no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs)
    · rcases h1 with ⟨_, hx⟩
      exact no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx)
    · rcases h2 with ⟨_, hx⟩
      exact no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx)

theorem no_sqStable_succ_from_nfUDecorLiftRightSPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfUDecorLiftRightSPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uDecorLiftRightSPredTerm := by
    simpa [nfUDecorLiftRightSPred] using hx.symm
  rcases plug_eq_uDecorLiftRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uDecorLiftRightPred t u hEq
  · rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
    have hy : NFSqStableStepCtx (α := V) nfXADecorRightPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXADecorRightPred] using hL.symm
    exact no_sqStable_succ_from_nfXADecorRightPred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' ((((t.op u).op (u.op u)).op u)) hS with h0 | h1 | h2
    · rcases h0 with ⟨rfl, hs⟩
      exact no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs)
    · rcases h1 with ⟨_, hx⟩
      exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
    · rcases h2 with ⟨_, hx⟩
      exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)

theorem decor_step_from_nfUDecorLiftRightSPred_eq_nfU {z : NormalForm V} :
    NFDecorStepCtx (α := V) nfUDecorLiftRightSPred z → z = nfU := by
  intro hz
  exact NFStepR_from_nfUDecorLiftRightSPred_eq_nfU (z := z)
    ⟨RuleId.Decor, by simp [R4], hz⟩

theorem no_c2c1_succ_from_nfUDecorLiftRightSPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfUDecorLiftRightSPred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uDecorLiftRightSPredTerm := by
    simpa [nfUDecorLiftRightSPred] using hx.symm
  rcases plug_eq_uDecorLiftRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_uDecorLiftRightPred x0 p z0 hEq
  · rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
    have hy : NFC2C1StepCtx (α := V) nfXADecorRightPred y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfXADecorRightPred] using hL.symm
    exact no_c2c1_succ_from_nfXADecorRightPred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hS with h0 | h1 | h2
    · rcases h0 with ⟨rfl, hs⟩
      exact no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs)
    · rcases h1 with ⟨_, hx⟩
      exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
    · rcases h2 with ⟨_, hx⟩
      exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)

theorem decorRightKernel_exact_support_theorem :
    (∀ {z : NormalForm V}, ¬ NFSqStepCtx (α := V) nfXADecorRightPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStepCtx (α := V) nfUDecorLiftRightSPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfXADecorRightPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUDecorLiftRightSPred z) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfXADecorRightPred z → z = nfXA) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorLiftRightSPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfXADecorRightPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUDecorLiftRightSPred z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact no_sqAbsorb_succ_from_nfXADecorRightPred (z := z) hz
  · intro z hz
    exact no_sqAbsorb_succ_from_nfUDecorLiftRightSPred (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfXADecorRightPred (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUDecorLiftRightSPred (z := z) hz
  · intro z hz
    exact decor_step_from_nfXADecorRightPred_eq_nfXA (z := z) hz
  · intro z hz
    exact decor_step_from_nfUDecorLiftRightSPred_eq_nfU (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfXADecorRightPred (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUDecorLiftRightSPred (z := z) hz

theorem decorRightKernel_exact_theorem :
    NFStepR (α := V) R4 nfXADecorRightPred nfXA ∧
    NFStepR (α := V) R4 nfUDecorLiftRightSPred nfU ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXADecorRightPred z → z = nfXA) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorLiftRightSPred z → z = nfU) ∧
    coreKernelSupportStatus .decorRightKernel = .exact := by
  refine ⟨nfXADecorRightPred_steps_to_nfXA, nfUDecorLiftRightSPred_steps_to_nfU, ?_, ?_, ?_⟩
  · intro z hz
    exact NFStepR_from_nfXADecorRightPred_eq_nfXA (z := z) hz
  · intro z hz
    exact NFStepR_from_nfUDecorLiftRightSPred_eq_nfU (z := z) hz
  · decide

theorem decorRightKernel_semantic_theorem :
    coreKernelRegime .decorRightKernel = .pure ∧
    coreKernelCodomainStatus .decorRightKernel = .settled ∧
    coreKernelSupportStatus .decorRightKernel = .exact := by
  decide

theorem no_sqAbsorb_succ_from_nfXADecorLeftPred {z : NormalForm V} :
    ¬ NFSqStepCtx (α := V) nfXADecorLeftPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = xADecorLeftSPredTerm := by
    simpa [nfXADecorLeftPred] using hx.symm
  rcases plug_eq_xADecorLeftPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqAbsorb_root_eq_xADecorLeftPred t u hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_sqAbsorb_lhs_eq_x C' t u hleft
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact sqAbsorb_right_succ_from_nfXADecorLeftPred_false hright hz

theorem no_sqStable_succ_from_nfXADecorLeftPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfXADecorLeftPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xADecorLeftSPredTerm := by
    simpa [nfXADecorLeftPred] using hx.symm
  rcases plug_eq_xADecorLeftPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_xADecorLeftPred t u hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_sqStable_lhs_eq_x C' t u hleft
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact sqStable_right_succ_from_nfXADecorLeftPred_false hright hz

theorem decor_step_from_nfXADecorLeftPred_eq_nfXA {z : NormalForm V} :
    NFDecorStepCtx (α := V) nfXADecorLeftPred z → z = nfXA := by
  intro hz
  exact NFStepR_from_nfXADecorLeftPred_eq_nfXA (z := z)
    ⟨RuleId.Decor, by simp [R4], hz⟩

theorem no_c2c1_succ_from_nfXADecorLeftPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfXADecorLeftPred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xADecorLeftSPredTerm := by
    simpa [nfXADecorLeftPred] using hx.symm
  rcases plug_eq_xADecorLeftPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_xADecorLeftPred x0 p z0 hEq
  · rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    exact c2c1_right_succ_from_nfXADecorLeftPred_false hright hz

theorem no_sqAbsorb_succ_from_nfUDecorLiftLeftSPred {z : NormalForm V} :
    ¬ NFSqStepCtx (α := V) nfUDecorLiftLeftSPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uDecorLiftLeftSPredTerm := by
    simpa [nfUDecorLiftLeftSPred] using hx.symm
  rcases plug_eq_uDecorLiftLeftPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqAbsorb_root_eq_uDecorLiftLeftPred t u hEq
  · rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' (t.op u)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' (t.op u)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' (t.op u)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u), hleftN⟩
    have hy : NFSqStepCtx (α := V) nfXADecorLeftPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXADecorLeftPred] using hL.symm
    exact no_sqAbsorb_succ_from_nfXADecorLeftPred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' (((t.op u).op (u.op u))) hS with h0 | h1 | h2
    · rcases h0 with ⟨rfl, hs⟩
      exact no_plug_sqAbsorb_lhs_eq_s Ctx.hole t u (by simpa using hs)
    · rcases h1 with ⟨_, hx⟩
      exact no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx)
    · rcases h2 with ⟨_, hx⟩
      exact no_plug_sqAbsorb_lhs_eq_x Ctx.hole t u (by simpa using hx)

theorem no_sqStable_succ_from_nfUDecorLiftLeftSPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfUDecorLiftLeftSPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uDecorLiftLeftSPredTerm := by
    simpa [nfUDecorLiftLeftSPred] using hx.symm
  rcases plug_eq_uDecorLiftLeftPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uDecorLiftLeftPred t u hEq
  · rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((t.op u).op (u.op u))).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((t.op u).op (u.op u))).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)), hleftN⟩
    have hy : NFSqStableStepCtx (α := V) nfXADecorLeftPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXADecorLeftPred] using hL.symm
    exact no_sqStable_succ_from_nfXADecorLeftPred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' ((((t.op u).op (u.op u)).op u)) hS with h0 | h1 | h2
    · rcases h0 with ⟨rfl, hs⟩
      exact no_plug_sqStable_lhs_eq_s Ctx.hole t u (by simpa using hs)
    · rcases h1 with ⟨_, hx⟩
      exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)
    · rcases h2 with ⟨_, hx⟩
      exact no_plug_sqStable_lhs_eq_x Ctx.hole t u (by simpa using hx)

theorem decor_step_from_nfUDecorLiftLeftSPred_eq_nfU {z : NormalForm V} :
    NFDecorStepCtx (α := V) nfUDecorLiftLeftSPred z → z = nfU := by
  intro hz
  exact NFStepR_from_nfUDecorLiftLeftSPred_eq_nfU (z := z)
    ⟨RuleId.Decor, by simp [R4], hz⟩

theorem no_c2c1_succ_from_nfUDecorLiftLeftSPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfUDecorLiftLeftSPred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uDecorLiftLeftSPredTerm := by
    simpa [nfUDecorLiftLeftSPred] using hx.symm
  rcases plug_eq_uDecorLiftLeftPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_uDecorLiftLeftPred x0 p z0 hEq
  · rcases hL with ⟨C', hC, hL⟩
    subst hC
    have hz' : z.1 = (Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s := by
      simpa [Ctx.plug] using hz
    have hzN : Normal (α := V) ((Ctx.plug C' ((x0.op (p.op z0)).op z0)).op s) := by
      simpa [hz'] using z.2
    have hleftN : Normal (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) :=
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1 hzN).1
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0), hleftN⟩
    have hy : NFC2C1StepCtx (α := V) nfXADecorLeftPred y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfXADecorLeftPred] using hL.symm
    exact no_c2c1_succ_from_nfXADecorLeftPred (z := y) hy
  · rcases hR with ⟨C', hC, hS⟩
    subst hC
    rcases plug_eq_s_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hS with h0 | h1 | h2
    · rcases h0 with ⟨rfl, hs⟩
      exact no_plug_c2c1_lhs_eq_s Ctx.hole x0 p z0 (by simpa using hs)
    · rcases h1 with ⟨_, hx⟩
      exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)
    · rcases h2 with ⟨_, hx⟩
      exact no_plug_c2c1_lhs_eq_x Ctx.hole x0 p z0 (by simpa using hx)

theorem decorLeftKernel_exact_support_theorem :
    (∀ {z : NormalForm V}, ¬ NFSqStepCtx (α := V) nfXADecorLeftPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStepCtx (α := V) nfUDecorLiftLeftSPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfXADecorLeftPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUDecorLiftLeftSPred z) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfXADecorLeftPred z → z = nfXA) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorLiftLeftSPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfXADecorLeftPred z) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUDecorLiftLeftSPred z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact no_sqAbsorb_succ_from_nfXADecorLeftPred (z := z) hz
  · intro z hz
    exact no_sqAbsorb_succ_from_nfUDecorLiftLeftSPred (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfXADecorLeftPred (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUDecorLiftLeftSPred (z := z) hz
  · intro z hz
    exact decor_step_from_nfXADecorLeftPred_eq_nfXA (z := z) hz
  · intro z hz
    exact decor_step_from_nfUDecorLiftLeftSPred_eq_nfU (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfXADecorLeftPred (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUDecorLiftLeftSPred (z := z) hz

theorem decorLeftKernel_exact_theorem :
    NFStepR (α := V) R4 nfXADecorLeftPred nfXA ∧
    NFStepR (α := V) R4 nfUDecorLiftLeftSPred nfU ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfXADecorLeftPred z → z = nfXA) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorLiftLeftSPred z → z = nfU) ∧
    coreKernelSupportStatus .decorLeftKernel = .exact := by
  refine ⟨nfXADecorLeftPred_steps_to_nfXA, nfUDecorLiftLeftSPred_steps_to_nfU, ?_, ?_, ?_⟩
  · intro z hz
    exact NFStepR_from_nfXADecorLeftPred_eq_nfXA (z := z) hz
  · intro z hz
    exact NFStepR_from_nfUDecorLiftLeftSPred_eq_nfU (z := z) hz
  · decide

theorem decorLeftKernel_semantic_theorem :
    coreKernelRegime .decorLeftKernel = .pure ∧
    coreKernelCodomainStatus .decorLeftKernel = .settled ∧
    coreKernelSupportStatus .decorLeftKernel = .exact := by
  decide

theorem sqAbsorb_succ_from_nfUDecorRightPred_eq_nfM {z : NormalForm V} :
    NFSqStepCtx (α := V) nfUDecorRightPred z → z = nfM := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C (((t.op u).op (u.op u))) = uDecorRightPredTerm := by
    simpa [nfUDecorRightPred] using hx.symm
  rcases plug_eq_uDecorRightPred_lhs_cases C (((t.op u).op (u.op u))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact False.elim (no_sqAbsorb_root_eq_uDecorRightPred t u hEq)
  · rcases hL with ⟨C', hC, hleft⟩
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
      NFStepR_from_nfXA_eq_nfV (z := y) (by exact ⟨RuleId.SqAbsorb, by simp [R4], hy⟩)
    have hyVal : y.1 = vTerm := by
      simpa [nfV] using congrArg Subtype.val hyEq
    exact eq_nfM_of_left_val hz' hyVal
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sv_rhs_cases C' (((t.op u).op (u.op u))) hright with h0 | hS | hV
    · rcases h0 with ⟨rfl, hEq⟩
      exact False.elim (no_sqAbsorb_rhs_root_eq_sv t u hEq)
    · rcases hS with ⟨C'', hC'', hs⟩
      subst hC''
      exact False.elim (no_plug_sqAbsorb_lhs_eq_s C'' t u hs)
    · rcases hV with ⟨C'', hC'', hv⟩
      subst hC''
      exact False.elim (no_plug_sqAbsorb_lhs_eq_vTerm C'' t u hv)

theorem no_sqStable_succ_from_nfUDecorRightPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfUDecorRightPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uDecorRightPredTerm := by
    simpa [nfUDecorRightPred] using hx.symm
  rcases plug_eq_uDecorRightPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uDecorRightPred t u hEq
  · rcases hL with ⟨C', hC, hleft⟩
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
    exact no_sqStable_succ_from_nfXA (z := y) hy
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sv_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hright with h0 | hS | hV
    · rcases h0 with ⟨rfl, hEq⟩
      exact no_sqStable_rhs_root_eq_sv t u hEq
    · rcases hS with ⟨C'', hC'', hs⟩
      subst hC''
      exact no_plug_sqStable_lhs_eq_s C'' t u hs
    · rcases hV with ⟨C'', hC'', hv⟩
      subst hC''
      exact no_plug_sqStable_lhs_eq_vTerm C'' t u hv

theorem no_c2c1_succ_from_nfUDecorRightPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfUDecorRightPred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uDecorRightPredTerm := by
    simpa [nfUDecorRightPred] using hx.symm
  rcases plug_eq_uDecorRightPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with h0 | hL | hR
  · rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_uDecorRightPred x0 p z0 hEq
  · rcases hL with ⟨C', hC, hleft⟩
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
    exact no_c2c1_succ_from_nfXA (z := y) hy
  · rcases hR with ⟨C', hC, hright⟩
    subst hC
    rcases plug_eq_sv_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hright with h0 | hS | hV
    · rcases h0 with ⟨rfl, hEq⟩
      exact no_c2c1_lhs_root_eq_sv x0 p z0 hEq
    · rcases hS with ⟨C'', hC'', hs⟩
      subst hC''
      exact no_plug_c2c1_lhs_eq_s C'' x0 p z0 hs
    · rcases hV with ⟨C'', hC'', hv⟩
      subst hC''
      exact no_plug_c2c1_lhs_eq_vTerm C'' x0 p z0 hv

theorem bridgeKernel_exact_support_theorem :
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUDecorRightPred z → z = nfM) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUDecorRightPred z) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorRightPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUDecorRightPred z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sqAbsorb_succ_from_nfUDecorRightPred_eq_nfM (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUDecorRightPred (z := z) hz
  · intro z hz
    exact decor_succ_from_nfUDecorRightPred_eq_nfU (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUDecorRightPred (z := z) hz

theorem bridgeKernel_rulewise_envelope_theorem :
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUDecorRightPred z → z = nfM) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorRightPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorRightPred z → z = nfU ∨ z = nfM) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact sqAbsorb_succ_from_nfUDecorRightPred_eq_nfM (z := z) hz
  · intro z hz
    exact decor_succ_from_nfUDecorRightPred_eq_nfU (z := z) hz
  · intro z hz
    exact NFStepR_from_nfUDecorRightPred_cases (z := z) hz

theorem bridgeKernel_exact_theorem :
    NFStepR (α := V) R4 nfUDecorRightPred nfM ∧
    NFDecorStepCtx (α := V) nfUDecorRightPred nfU ∧
    (∀ {z : NormalForm V}, NFSqStepCtx (α := V) nfUDecorRightPred z → z = nfM) ∧
    (∀ {z : NormalForm V}, ¬ NFSqStableStepCtx (α := V) nfUDecorRightPred z) ∧
    (∀ {z : NormalForm V}, NFDecorStepCtx (α := V) nfUDecorRightPred z → z = nfU) ∧
    (∀ {z : NormalForm V}, ¬ NFC2C1StepCtx (α := V) nfUDecorRightPred z) ∧
    (∀ {z : NormalForm V}, NFStepR (α := V) R4 nfUDecorRightPred z → z = nfU ∨ z = nfM) := by
  refine ⟨nfUDecorRightPred_steps_to_nfM, nfUDecorRightPred_decor_to_nfU, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact sqAbsorb_succ_from_nfUDecorRightPred_eq_nfM (z := z) hz
  · intro z hz
    exact no_sqStable_succ_from_nfUDecorRightPred (z := z) hz
  · intro z hz
    exact decor_succ_from_nfUDecorRightPred_eq_nfU (z := z) hz
  · intro z hz
    exact no_c2c1_succ_from_nfUDecorRightPred (z := z) hz
  · intro z hz
    exact NFStepR_from_nfUDecorRightPred_cases (z := z) hz

theorem bridgeKernel_semantic_theorem :
    coreKernelRegime .bridgeKernel = .bridgeSplit ∧
    coreKernelCodomainStatus .bridgeKernel = .settled ∧
    coreKernelSupportStatus .bridgeKernel = .exact := by
  decide

theorem coreKernelSemanticCompletion :
    coreKernelCodomainStatus .saKernel = .settled ∧
    coreKernelSupportStatus .saKernel = .exact ∧
    coreKernelRegime .saKernel = .pure ∧
    coreKernelCodomainStatus .decorRightKernel = .settled ∧
    coreKernelSupportStatus .decorRightKernel = .exact ∧
    coreKernelRegime .decorRightKernel = .pure ∧
    coreKernelCodomainStatus .decorLeftKernel = .settled ∧
    coreKernelSupportStatus .decorLeftKernel = .exact ∧
    coreKernelRegime .decorLeftKernel = .pure ∧
    coreKernelCodomainStatus .aaKernel = .settled ∧
    coreKernelSupportStatus .aaKernel = .exact ∧
    coreKernelRegime .aaKernel = .pure ∧
    coreKernelCodomainStatus .stableKernel = .settled ∧
    coreKernelSupportStatus .stableKernel = .exact ∧
    coreKernelRegime .stableKernel = .pure ∧
    coreKernelCodomainStatus .holeKernel = .settled ∧
    coreKernelSupportStatus .holeKernel = .exact ∧
    coreKernelRegime .holeKernel = .pure ∧
    coreKernelCodomainStatus .decorHoleKernel = .settled ∧
    coreKernelSupportStatus .decorHoleKernel = .exact ∧
    coreKernelRegime .decorHoleKernel = .pure ∧
    coreKernelCodomainStatus .bridgeKernel = .settled ∧
    coreKernelSupportStatus .bridgeKernel = .exact ∧
    coreKernelRegime .bridgeKernel = .bridgeSplit := by
  decide

theorem coreKernelProvisionalCompletion :
    coreKernelStatus .saKernel = .settled ∧
    coreKernelStatus .decorRightKernel = .settled ∧
    coreKernelStatus .decorLeftKernel = .settled ∧
    coreKernelStatus .aaKernel = .settled ∧
    coreKernelStatus .stableKernel = .settled ∧
    coreKernelStatus .holeKernel = .settled ∧
    coreKernelStatus .decorHoleKernel = .settled ∧
    coreKernelStatus .bridgeKernel = .settled := by
  decide

theorem no_sqStable_succ_from_nfXASqAPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfXASqAPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = xASqAPredTerm := by
    simpa [nfXASqAPred] using hx.symm
  rcases plug_eq_xASqAPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_xASqAPred t u hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_sqStable_lhs_eq_x C' t u hleft
  ·
    rcases hR with ⟨C', hC, hAA⟩
    subst hC
    rcases plug_eq_AA_rhs_cases C' ((((t.op u).op (u.op u)).op u)) hAA with
      hAA0 | hAA1 | hAA2
    ·
      rcases hAA0 with ⟨rfl, hEq⟩
      exact no_sqStable_root_eq_AA t u hEq
    ·
      rcases hAA1 with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_sqStable_lhs_eq_A C'' t u hAeq
    ·
      rcases hAA2 with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_sqStable_lhs_eq_A C'' t u hAeq

theorem no_decor_succ_from_nfXASqAPred {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfXASqAPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = xASqAPredTerm := by
    simpa [nfXASqAPred] using hx.symm
  rcases plug_eq_xASqAPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_decor_root_eq_xASqAPred t u hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_decor_lhs_eq_x C' t u hleft
  ·
    rcases hR with ⟨C', hC, hAA⟩
    subst hC
    rcases plug_eq_AA_rhs_cases C' ((t.op u).op (u.op (u.op u))) hAA with
      hAA0 | hAA1 | hAA2
    ·
      rcases hAA0 with ⟨rfl, hEq⟩
      exact no_decor_root_eq_AA t u hEq
    ·
      rcases hAA1 with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_decor_lhs_eq_A C'' t u hAeq
    ·
      rcases hAA2 with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_decor_lhs_eq_A C'' t u hAeq

theorem no_c2c1_succ_from_nfXASqAPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfXASqAPred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = xASqAPredTerm := by
    simpa [nfXASqAPred] using hx.symm
  rcases plug_eq_xASqAPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_xASqAPred x0 p z0 hEq
  ·
    rcases hL with ⟨C', hC, hleft⟩
    subst hC
    exact no_plug_c2c1_lhs_eq_x C' x0 p z0 hleft
  ·
    rcases hR with ⟨C', hC, hAA⟩
    subst hC
    rcases plug_eq_AA_rhs_cases C' ((((x0.op (p.op z0)).op z0).op (p.op z0))) hAA with
      hAA0 | hAA1 | hAA2
    ·
      rcases hAA0 with ⟨rfl, hEq⟩
      exact no_c2c1_root_eq_AA x0 p z0 hEq
    ·
      rcases hAA1 with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_c2c1_lhs_eq_A C'' x0 p z0 hAeq
    ·
      rcases hAA2 with ⟨C'', hC'', hAeq⟩
      subst hC''
      exact no_plug_c2c1_lhs_eq_A C'' x0 p z0 hAeq

theorem no_sqStable_succ_from_nfUSqLiftAPred {z : NormalForm V} :
    ¬ NFSqStableStepCtx (α := V) nfUSqLiftAPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((((t.op u).op (u.op u)).op u)) = uSqLiftAPredTerm := by
    simpa [nfUSqLiftAPred] using hx.symm
  rcases plug_eq_uSqLiftAPred_lhs_cases C ((((t.op u).op (u.op u)).op u)) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_sqStable_root_eq_uSqLiftAPred t u hEq
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    let y : NormalForm V := ⟨Ctx.plug C' ((t.op u).op (u.op u)),
      ((Normal_op_iff (α := V) (Ctx.plug C' ((t.op u).op (u.op u))) s).1
        (by simpa [hz] using z.2)).1⟩
    have hy : NFSqStableStepCtx (α := V) nfXASqAPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXASqAPred] using hL.symm
    exact no_sqStable_succ_from_nfXASqAPred (z := y) hy
  ·
    rcases hR with ⟨C', rfl, hS⟩
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

theorem no_decor_succ_from_nfUSqLiftAPred {z : NormalForm V} :
    ¬ NFDecorStepCtx (α := V) nfUSqLiftAPred z := by
  rintro ⟨C, t, u, hx, hz⟩
  have hx' : Ctx.plug C ((t.op u).op (u.op (u.op u))) = uSqLiftAPredTerm := by
    simpa [nfUSqLiftAPred] using hx.symm
  rcases plug_eq_uSqLiftAPred_lhs_cases C ((t.op u).op (u.op (u.op u))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_decor_root_eq_uSqLiftAPred t u hEq
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    let y : NormalForm V := ⟨Ctx.plug C' (t.op u),
      ((Normal_op_iff (α := V) (Ctx.plug C' (t.op u)) s).1
        (by simpa [hz] using z.2)).1⟩
    have hy : NFDecorStepCtx (α := V) nfXASqAPred y := by
      refine ⟨C', t, u, ?_, rfl⟩
      simpa [nfXASqAPred] using hL.symm
    exact no_decor_succ_from_nfXASqAPred (z := y) hy
  ·
    rcases hR with ⟨C', rfl, hS⟩
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

theorem no_c2c1_succ_from_nfUSqLiftAPred {z : NormalForm V} :
    ¬ NFC2C1StepCtx (α := V) nfUSqLiftAPred z := by
  rintro ⟨C, x0, p, z0, hx, hz⟩
  have hx' : Ctx.plug C ((((x0.op (p.op z0)).op z0).op (p.op z0))) = uSqLiftAPredTerm := by
    simpa [nfUSqLiftAPred] using hx.symm
  rcases plug_eq_uSqLiftAPred_lhs_cases C ((((x0.op (p.op z0)).op z0).op (p.op z0))) hx' with
    h0 | hL | hR
  ·
    rcases h0 with ⟨rfl, hEq⟩
    exact no_c2c1_root_eq_uSqLiftAPred x0 p z0 hEq
  ·
    rcases hL with ⟨C', hC, hL⟩
    subst hC
    let y : NormalForm V := ⟨Ctx.plug C' ((x0.op (p.op z0)).op z0),
      ((Normal_op_iff (α := V) (Ctx.plug C' ((x0.op (p.op z0)).op z0)) s).1
        (by simpa [hz] using z.2)).1⟩
    have hy : NFC2C1StepCtx (α := V) nfXASqAPred y := by
      refine ⟨C', x0, p, z0, ?_, rfl⟩
      simpa [nfXASqAPred] using hL.symm
    exact no_c2c1_succ_from_nfXASqAPred (z := y) hy
  ·
    rcases hR with ⟨C', rfl, hS⟩
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


end CoreKernelTheorems

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
