import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

namespace WeakAbsorption.Proof.Generators.Vars1.Independence.Witness

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA

abbrev V : Type := Fin 1

def x : Term V := .var 0
def s : Term V := x.op x
def A : Term V := s.op s

-- DoubleSq witness (t=x, u=x):
-- LHS = (x ⋆ ((s⋆s))) ⋆ s = (x ⋆ A) ⋆ s
-- RHS = x ⋆ s
def vTerm : Term V := x.op s
def uTerm : Term V := (x.op A).op s

-- ---- Normality (straight structural, no search) ----

private theorem x_normal : Normal (α := V) x := by
  intro u hu
  nomatch hu

private theorem s_normal : Normal (α := V) s := by
  apply (Normal_op_iff (α := V) x x).2
  refine ⟨x_normal, x_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩; cases hw
  · simp [IsC2pRoot, x]

private theorem A_normal : Normal (α := V) A := by
  apply (Normal_op_iff (α := V) s s).2
  refine ⟨s_normal, s_normal, ?_, ?_⟩
  · -- ¬ IsC1Root s s
    rintro ⟨w, hw⟩
    -- would force s = w ⋆ s, but s is x⋆x so right child mismatch
    dsimp [s, x] at hw
    injection hw with hL hR
    cases hR
  · -- ¬ IsC2pRoot s s
    dsimp [IsC2pRoot, s, x]
    rintro ⟨w, hw⟩
    injection hw with h1 h2
    cases h1

private theorem v_normal : Normal (α := V) vTerm := by
  apply (Normal_op_iff (α := V) x s).2
  refine ⟨x_normal, s_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩; cases hw
  · dsimp [IsC2pRoot, s, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem xA_normal : Normal (α := V) (x.op A) := by
  apply (Normal_op_iff (α := V) x A).2
  refine ⟨x_normal, A_normal, ?_, ?_⟩
  · rintro ⟨w, hw⟩; cases hw
  · -- IsC2pRoot x A impossible (var = op ...)
    cases A <;> simp [IsC2pRoot, x]

private theorem u_normal : Normal (α := V) uTerm := by
  apply (Normal_op_iff (α := V) (x.op A) s).2
  refine ⟨xA_normal, s_normal, ?_, ?_⟩
  · -- ¬ IsC1Root (x⋆A) s
    rintro ⟨w, hw⟩
    injection hw with hL hR
    -- hR : A = s であることを利用
    dsimp [A, s, x] at hR
    -- (x⋆x)⋆(x⋆x) = x⋆x は構造的に不可能
    injection hR with hR_left hR_right
    -- (x⋆x) = x の矛盾
    injection hR_left
  · -- ¬ IsC2pRoot (x⋆A) s のケース
    rintro ⟨w, hw⟩
    injection hw with h1 h2
    -- h1 : x = w ⋆ x  ← ここで矛盾
    cases h1

def nfV : NormalForm V := ⟨vTerm, v_normal⟩
def nfU : NormalForm V := ⟨uTerm, u_normal⟩
def xATerm : Term V := x.op A
def nfXA : NormalForm V := ⟨xATerm, xA_normal⟩

theorem nfXA_ne_nfV : nfXA.1 ≠ nfV.1 := by
  intro h
  dsimp [nfXA, nfV, xATerm, vTerm, x, s, A] at h
  injection h with h1 h2
  -- h2 : (x ⋆ x) ⋆ (x ⋆ x) = x ⋆ x
  injection h2 with hL hR
  -- hL : (x ⋆ x) = x
  cases hL

theorem nfU_ne_nfXA : nfU.1 ≠ nfXA.1 := by
  intro h
  dsimp [nfU, nfXA, uTerm, xATerm, x, s, A] at h
  injection h with h1 h2
  -- h1 : x ⋆ A = x
  cases h1

theorem nfXA_steps_to_nfV :
    NFStepR (α := V) R4 nfXA nfV := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  · refine ⟨Ctx.right x Ctx.hole, x, x, ?_, ?_⟩
    ·
      change xATerm = Ctx.plug (Ctx.right x Ctx.hole) (((x.op x).op (x.op x)))
      simp [Ctx.plug, xATerm, A, s, x]
    ·
      change vTerm = Ctx.plug (Ctx.right x Ctx.hole) (x.op x)
      simp [Ctx.plug, vTerm, s, x]

-- ---- NFRel witness via the built-in DoubleSq derived RedEq ----
theorem nfRel_nfU_nfV : NFRel (α := V) nfU nfV := by
  -- use NFDoubleSqStepCtx → NFRel
  apply NFDoubleSqStepCtx_imp_NFRel (α := V)
  refine ⟨Ctx.hole, x, x, ?_, ?_⟩ <;> rfl

end WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
