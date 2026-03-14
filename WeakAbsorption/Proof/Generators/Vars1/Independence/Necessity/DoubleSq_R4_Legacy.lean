import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_KernelTheorems

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
open WAA


/-!
Legacy shell / VSpine / flow analysis extracted from the former monolithic
`DoubleSq_R4_Core`. These results record historical shell-based viewpoints and
terminal-flow arguments, while the main kernel API lives elsewhere.
-/

theorem NFStepR_to_nfU_cases {z : NormalForm V} :
    NFStepR (α := V) R4 z nfU →
      z = nfUHolePred ∨
      z = nfUSqLiftHolePred ∨
      z = nfUSqLiftAPred ∨
      z = nfUSqLiftRightSPred ∨
      z = nfUStablePred ∨
      z = nfUDecorHolePred ∨
      z = nfUDecorLiftHolePred ∨
      z = nfUDecorLiftAPred ∨
      z = nfUDecorLiftLeftSPred ∨
      z = nfUDecorLiftRightSPred ∨
      z = nfUDecorRightPred := by
  intro h
  rcases NFStepR_to_nfU_actual_cases (z := z) h with
    h | h | h | h | h | h | h | h | h | h | h
  ·
    exact Or.inl (Subtype.ext (by simpa [nfUHolePred] using h))
  ·
    exact Or.inr (Or.inl (Subtype.ext (by simpa [nfUSqLiftHolePred] using h)))
  ·
    exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUSqLiftAPred] using h))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUSqLiftRightSPred] using h)))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUStablePred] using h))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUDecorHolePred] using h)))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUDecorLiftHolePred] using h))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUDecorLiftAPred] using h)))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUDecorLiftLeftSPred] using h))))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [nfUDecorLiftRightSPred] using h)))))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext (by simpa [nfUDecorRightPred] using h)))))))))))

theorem NFStepR_to_nfU_iff (z : NormalForm V) :
    NFStepR (α := V) R4 z nfU ↔
      z = nfUHolePred ∨
      z = nfUSqLiftHolePred ∨
      z = nfUSqLiftAPred ∨
      z = nfUSqLiftRightSPred ∨
      z = nfUStablePred ∨
      z = nfUDecorHolePred ∨
      z = nfUDecorLiftHolePred ∨
      z = nfUDecorLiftAPred ∨
      z = nfUDecorLiftLeftSPred ∨
      z = nfUDecorLiftRightSPred ∨
      z = nfUDecorRightPred := by
  constructor
  · intro h
    exact NFStepR_to_nfU_cases (z := z) h
  · intro h
    rcases h with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact nfUHolePred_steps_to_nfU
    · exact nfUSqLiftHolePred_steps_to_nfU
    · exact nfUSqLiftAPred_steps_to_nfU
    · exact nfUSqLiftRightSPred_steps_to_nfU
    · exact nfUStablePred_steps_to_nfU
    · exact nfUDecorHolePred_steps_to_nfU
    · exact nfUDecorLiftHolePred_steps_to_nfU
    · exact nfUDecorLiftAPred_steps_to_nfU
    · exact nfUDecorLiftLeftSPred_steps_to_nfU
    · exact nfUDecorLiftRightSPred_steps_to_nfU
    · exact nfUDecorRightPred_steps_to_nfU

theorem NFAdjR_at_nfU_iff (z : NormalForm V) :
    NFAdjR (α := V) R4 nfU z ↔
      z = nfUHolePred ∨
      z = nfUSqLiftHolePred ∨
      z = nfUSqLiftAPred ∨
      z = nfUSqLiftRightSPred ∨
      z = nfUStablePred ∨
      z = nfUDecorHolePred ∨
      z = nfUDecorLiftHolePred ∨
      z = nfUDecorLiftAPred ∨
      z = nfUDecorLiftLeftSPred ∨
      z = nfUDecorLiftRightSPred ∨
      z = nfUDecorRightPred := by
  constructor
  ·
    intro h
    rcases h with h | h
    · exact False.elim (no_NFStepR_from_nfU (z := z) h)
    · exact (NFStepR_to_nfU_iff (z := z)).1 h
  ·
    intro h
    exact Or.inr <| (NFStepR_to_nfU_iff (z := z)).2 h


def UShell : NormalForm V → Prop
  | z =>
      z = nfU ∨
      z = nfUHolePred ∨
      z = nfUSqLiftHolePred ∨
      z = nfUSqLiftAPred ∨
      z = nfUSqLiftRightSPred ∨
      z = nfUStablePred ∨
      z = nfUDecorHolePred ∨
      z = nfUDecorLiftHolePred ∨
      z = nfUDecorLiftAPred ∨
      z = nfUDecorLiftLeftSPred ∨
      z = nfUDecorLiftRightSPred ∨
      z = nfUDecorRightPred ∨
      z = nfM
/-
private theorem UShell_nfU : UShell nfU := by
  exact Or.inl rfl
-/
private theorem UShell_of_NFAdjR_at_nfU {z : NormalForm V} :
    NFAdjR (α := V) R4 nfU z → UShell z := by
  intro hAdj
  rcases (NFAdjR_at_nfU_iff (z := z)).1 hAdj with
    h | h | h | h | h | h | h | h | h | h | h <;>
    simp [UShell, h]
    /-
private theorem UShell_nfM : UShell nfM := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))
-/
private theorem UShell_nfU : UShell nfU := by
  simp [UShell]

private theorem UShell_nfM : UShell nfM := by
  simp [UShell]

theorem NFStepR_from_nfUStablePred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUStablePred z → UShell z := by
  intro h
  rw [NFStepR_from_nfUStablePred_eq_nfU (z := z) h]
  simp [UShell]

theorem NFStepR_from_nfUHolePred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUHolePred z → UShell z := by
  intro h
  rw [NFStepR_from_nfUHolePred_eq_nfU (z := z) h]
  simp [UShell]

theorem NFStepR_from_nfUDecorHolePred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorHolePred z → UShell z := by
  intro h
  rcases NFStepR_from_nfUDecorHolePred_cases (z := z) h with h' | h'
  ·
    rw [h']
    simp [UShell]
  ·
    rw [h']
    simp [UShell]

theorem NFStepR_from_nfUDecorRightPred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorRightPred z → UShell z := by
  intro h
  rcases NFStepR_from_nfUDecorRightPred_cases (z := z) h with h' | h'
  ·
    rw [h']
    simp [UShell]
  ·
    rw [h']
    simp [UShell]

theorem UShell_of_NFStepR_from_nfU {z : NormalForm V} :
    NFStepR (α := V) R4 nfU z → UShell z := by
  intro h
  exact UShell_of_NFAdjR_at_nfU (z := z) (Or.inl h)

private theorem UShell_forward_closed_known {u v : NormalForm V} :
    (u = nfU ∨
      u = nfUHolePred ∨
      u = nfUStablePred ∨
      u = nfUDecorHolePred ∨
      u = nfUDecorRightPred ∨
      u = nfM) →
    NFStepR (α := V) R4 u v →
    UShell v := by
  intro hu hstep
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact UShell_of_NFStepR_from_nfU (z := v) hstep
  ·
    exact NFStepR_from_nfUHolePred_in_UShell (z := v) hstep
  ·
    exact NFStepR_from_nfUStablePred_in_UShell (z := v) hstep
  ·
    exact NFStepR_from_nfUDecorHolePred_in_UShell (z := v) hstep
  ·
    exact NFStepR_from_nfUDecorRightPred_in_UShell (z := v) hstep
  ·
    exact False.elim (no_NFStepR_from_nfM (z := v) hstep)

private theorem UShell_forward_closed_core {u v : NormalForm V} :
    UShell u →
    (u = nfU ∨
      u = nfUHolePred ∨
      u = nfUStablePred ∨
      u = nfUDecorHolePred ∨
      u = nfUDecorRightPred ∨
      u = nfM) →
    NFStepR (α := V) R4 u v →
    UShell v := by
  intro _ hu hstep
  exact UShell_forward_closed_known (u := u) (v := v) hu hstep



theorem NFStepR_from_nfUSqLiftRightSPred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUSqLiftRightSPred z → UShell z := by
  intro h
  rw [NFStepR_from_nfUSqLiftRightSPred_eq_nfU (z := z) h]
  simp [UShell]

theorem NFStepR_from_nfUDecorLiftRightSPred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorLiftRightSPred z → UShell z := by
  intro h
  rw [NFStepR_from_nfUDecorLiftRightSPred_eq_nfU (z := z) h]
  simp [UShell]

def uSqLiftHoleEscapeTerm : Term V :=
  (vTerm.op (A.op A)).op s

private theorem uSqLiftHoleEscape_normal :
    Normal (α := V) uSqLiftHoleEscapeTerm := by
  apply (Normal_op_iff (α := V) (vTerm.op (A.op A)) s).2
  refine ⟨?_, s_normal_from_nfV, ?_, ?_⟩
  ·
    apply (Normal_op_iff (α := V) vTerm (A.op A)).2
    refine ⟨nfV.2, AA_normal, ?_, ?_⟩
    ·
      rintro ⟨w, hw⟩
      dsimp [vTerm, A, s, x] at hw
      injection hw with hL hR
      cases hR
    ·
      dsimp [IsC2pRoot, vTerm, A, s, x]
      rintro ⟨w, hw⟩
      cases hw
  ·
    rintro ⟨w, hw⟩
    dsimp [uSqLiftHoleEscapeTerm, vTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uSqLiftHoleEscapeTerm, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUSqLiftHoleEscape : NormalForm V :=
  ⟨uSqLiftHoleEscapeTerm, uSqLiftHoleEscape_normal⟩

private theorem nfUSqLiftHolePred_steps_to_escape :
    NFStepR (α := V) R4 nfUSqLiftHolePred nfUSqLiftHoleEscape := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.left (Ctx.right x Ctx.hole) (A.op A)) s, x, x, ?_, ?_⟩
    ·
      change uSqLiftHolePredTerm
        = Ctx.plug (Ctx.left (Ctx.left (Ctx.right x Ctx.hole) (A.op A)) s)
            (((x.op x).op (x.op x)))
      simp [Ctx.plug, uSqLiftHolePredTerm, xASqHolePredTerm, xATerm, A, s, x]
    ·
      change uSqLiftHoleEscapeTerm
        = Ctx.plug (Ctx.left (Ctx.left (Ctx.right x Ctx.hole) (A.op A)) s)
            (x.op x)
      simp [Ctx.plug, uSqLiftHoleEscapeTerm, vTerm, A, s, x]

private theorem nfUSqLiftHoleEscape_not_in_UShell :
    ¬ UShell nfUSqLiftHoleEscape := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfU] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uSqLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUSqLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uSqLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUSqLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uSqLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUSqLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uStablePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUStablePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uDecorHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUDecorHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uDecorLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUDecorLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uDecorLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUDecorLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uDecorLiftLeftSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUDecorLiftLeftSPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uDecorLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUDecorLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ uDecorRightPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfUDecorRightPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeTerm ≠ mTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscape, nfM] using congrArg Subtype.val h


theorem exists_step_from_nfUSqLiftHolePred_outside_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUSqLiftHolePred z ∧ ¬ UShell z := by
  refine ⟨nfUSqLiftHoleEscape, nfUSqLiftHolePred_steps_to_escape, ?_⟩
  exact nfUSqLiftHoleEscape_not_in_UShell

def uDecorLiftHoleEscapeTerm : Term V :=
  (vTerm.op (A.op (A.op A))).op s

private theorem uDecorLiftHoleEscape_normal :
    Normal (α := V) uDecorLiftHoleEscapeTerm := by
  apply (Normal_op_iff (α := V) (vTerm.op (A.op (A.op A))) s).2
  refine ⟨?_, s_normal_from_nfV, ?_, ?_⟩
  ·
    apply (Normal_op_iff (α := V) vTerm (A.op (A.op A))).2
    refine ⟨nfV.2, A_AA_normal, ?_, ?_⟩
    ·
      rintro ⟨w, hw⟩
      dsimp [vTerm, A, s, x] at hw
      injection hw with hL hR
      cases hR
    ·
      dsimp [IsC2pRoot, vTerm, A, s, x]
      rintro ⟨w, hw⟩
      cases hw
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorLiftHoleEscapeTerm, vTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorLiftHoleEscapeTerm, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUDecorLiftHoleEscape : NormalForm V :=
  ⟨uDecorLiftHoleEscapeTerm, uDecorLiftHoleEscape_normal⟩

private theorem nfUDecorLiftHolePred_steps_to_escape :
    NFStepR (α := V) R4 nfUDecorLiftHolePred nfUDecorLiftHoleEscape := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.left (Ctx.right x Ctx.hole) (A.op (A.op A))) s, x, x, ?_, ?_⟩
    ·
      change uDecorLiftHolePredTerm
        = Ctx.plug (Ctx.left (Ctx.left (Ctx.right x Ctx.hole) (A.op (A.op A))) s)
            (((x.op x).op (x.op x)))
      simp [Ctx.plug, uDecorLiftHolePredTerm, xADecorHolePredTerm, xATerm, A, s, x]
    ·
      change uDecorLiftHoleEscapeTerm
        = Ctx.plug (Ctx.left (Ctx.left (Ctx.right x Ctx.hole) (A.op (A.op A))) s)
            (x.op x)
      simp [Ctx.plug, uDecorLiftHoleEscapeTerm, vTerm, A, s, x]

private theorem nfUDecorLiftHoleEscape_not_in_UShell :
    ¬ UShell nfUDecorLiftHoleEscape := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfU] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uSqLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUSqLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uSqLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUSqLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uSqLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUSqLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uStablePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUStablePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uDecorHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUDecorHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uDecorLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUDecorLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uDecorLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUDecorLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uDecorLiftLeftSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUDecorLiftLeftSPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uDecorLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUDecorLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ uDecorRightPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfUDecorRightPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftHoleEscapeTerm ≠ mTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftHoleEscape, nfM] using congrArg Subtype.val h

theorem exists_step_from_nfUDecorLiftHolePred_outside_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftHolePred z ∧ ¬ UShell z := by
  refine ⟨nfUDecorLiftHoleEscape, nfUDecorLiftHolePred_steps_to_escape, ?_⟩
  exact nfUDecorLiftHoleEscape_not_in_UShell

theorem UShell_not_forward_closed :
    ¬ (∀ u v : NormalForm V,
        UShell u → NFStepR (α := V) R4 u v → UShell v) := by
  intro hclosed
  rcases exists_step_from_nfUSqLiftHolePred_outside_UShell with ⟨z, hzStep, hzOut⟩
  apply hzOut
  exact hclosed nfUSqLiftHolePred z (by simp [UShell]) hzStep

theorem UShell_not_forward_closed' :
    ¬ (∀ u v : NormalForm V,
        UShell u → NFAdjR (α := V) R4 u v → UShell v) := by
  intro hclosed
  rcases exists_step_from_nfUSqLiftHolePred_outside_UShell with ⟨z, hzStep, hzOut⟩
  apply hzOut
  exact hclosed nfUSqLiftHolePred z (by simp [UShell]) (Or.inl hzStep)

theorem NFStepR_from_nfUSqLiftAPred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUSqLiftAPred z → UShell z := by
  intro h
  rcases NFStepR_from_nfUSqLiftAPred_cases (z := z) h with hU | hR
  · rw [hU]; simp [UShell]
  · rw [hR]; simp [UShell]

def uDecorLiftAPredLeftEscapeTerm : Term V :=
  (x.op (s.op (s.op A))).op s

private theorem ssA_normal :
    Normal (α := V) (s.op (s.op A)) := by
  apply (Normal_op_iff (α := V) s (s.op A)).2
  refine ⟨s_normal_from_nfV, sA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, A, s, x]
    rintro ⟨w, hw⟩
    injection hw with hL hR
    cases hL

private theorem xDecorAPredLeftEscape_normal :
    Normal (α := V) (x.op (s.op (s.op A))) := by
  apply (Normal_op_iff (α := V) x (s.op (s.op A))).2
  refine ⟨x_normal_from_nfV, ssA_normal, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    cases hw
  ·
    dsimp [IsC2pRoot, A, s, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem uDecorLiftAPredLeftEscape_normal :
    Normal (α := V) uDecorLiftAPredLeftEscapeTerm := by
  apply (Normal_op_iff (α := V) (x.op (s.op (s.op A))) s).2
  refine ⟨xDecorAPredLeftEscape_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uDecorLiftAPredLeftEscapeTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uDecorLiftAPredLeftEscapeTerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUDecorLiftAPredLeftEscape : NormalForm V :=
  ⟨uDecorLiftAPredLeftEscapeTerm, uDecorLiftAPredLeftEscape_normal⟩

private theorem nfUDecorLiftAPred_steps_to_left_escape :
    NFStepR (α := V) R4 nfUDecorLiftAPred nfUDecorLiftAPredLeftEscape := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right x (Ctx.left Ctx.hole (s.op A))) s, x, x, ?_, ?_⟩
    ·
      change uDecorLiftAPredTerm
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole (s.op A))) s)
            (((x.op x).op (x.op x)))
      simp [Ctx.plug, uDecorLiftAPredTerm, xADecorAPredTerm, A, s, x]
    ·
      change uDecorLiftAPredLeftEscapeTerm
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.left Ctx.hole (s.op A))) s)
            (x.op x)
      simp [Ctx.plug, uDecorLiftAPredLeftEscapeTerm, A, s, x]

private theorem nfUDecorLiftAPredLeftEscape_not_in_UShell :
    ¬ UShell nfUDecorLiftAPredLeftEscape := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfU] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uSqLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUSqLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uSqLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUSqLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uSqLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUSqLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uStablePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUStablePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uDecorHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUDecorHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uDecorLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUDecorLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uDecorLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUDecorLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uDecorLiftLeftSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUDecorLiftLeftSPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uDecorLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUDecorLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ uDecorRightPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfUDecorRightPred] using congrArg Subtype.val h
  ·
    have hneq : uDecorLiftAPredLeftEscapeTerm ≠ mTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUDecorLiftAPredLeftEscape, nfM] using congrArg Subtype.val h

theorem exists_step_from_nfUDecorLiftAPred_outside_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftAPred z ∧ ¬ UShell z := by
  refine ⟨nfUDecorLiftAPredLeftEscape, nfUDecorLiftAPred_steps_to_left_escape, ?_⟩
  exact nfUDecorLiftAPredLeftEscape_not_in_UShell

def uSqLiftHoleEscapeCollapseTerm : Term V :=
  (vTerm.op A).op s

private theorem vA_normal :
    Normal (α := V) (vTerm.op A) := by
  apply (Normal_op_iff (α := V) vTerm A).2
  refine ⟨nfV.2, A_normal_from_nfXA, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [vTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    cases hw

private theorem uSqLiftHoleEscapeCollapse_normal :
    Normal (α := V) uSqLiftHoleEscapeCollapseTerm := by
  apply (Normal_op_iff (α := V) (vTerm.op A) s).2
  refine ⟨vA_normal, s_normal_from_nfV, ?_, ?_⟩
  ·
    rintro ⟨w, hw⟩
    dsimp [uSqLiftHoleEscapeCollapseTerm, vTerm, A, s, x] at hw
    nomatch hw
  ·
    dsimp [IsC2pRoot, uSqLiftHoleEscapeCollapseTerm, vTerm, A, s, x]
    rintro ⟨w, hw⟩
    nomatch hw

def nfUSqLiftHoleEscapeCollapse : NormalForm V :=
  ⟨uSqLiftHoleEscapeCollapseTerm, uSqLiftHoleEscapeCollapse_normal⟩

private theorem nfUSqLiftHoleEscape_steps_to_collapse :
    NFStepR (α := V) R4 nfUSqLiftHoleEscape nfUSqLiftHoleEscapeCollapse := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right vTerm Ctx.hole) s, s, s, ?_, ?_⟩
    ·
      change uSqLiftHoleEscapeTerm
        = Ctx.plug (Ctx.left (Ctx.right vTerm Ctx.hole) s)
            (((s.op s).op (s.op s)))
      simp [Ctx.plug, uSqLiftHoleEscapeTerm, vTerm, A, s, x]
    ·
      change uSqLiftHoleEscapeCollapseTerm
        = Ctx.plug (Ctx.left (Ctx.right vTerm Ctx.hole) s)
            (s.op s)
      simp [Ctx.plug, uSqLiftHoleEscapeCollapseTerm, vTerm, A, s, x]


private theorem nfUSqLiftHoleEscapeCollapse_not_in_UShell :
    ¬ UShell nfUSqLiftHoleEscapeCollapse := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfU] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uSqLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUSqLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uSqLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUSqLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uSqLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUSqLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uStablePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUStablePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uDecorHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUDecorHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uDecorLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUDecorLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uDecorLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUDecorLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uDecorLiftLeftSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUDecorLiftLeftSPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uDecorLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUDecorLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ uDecorRightPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfUDecorRightPred] using congrArg Subtype.val h
  ·
    have hneq : uSqLiftHoleEscapeCollapseTerm ≠ mTerm := by
      native_decide
    exact hneq <| by
      simpa [nfUSqLiftHoleEscapeCollapse, nfM] using congrArg Subtype.val h

theorem exists_step_from_nfUSqLiftHoleEscape_outside_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUSqLiftHoleEscape z ∧ ¬ UShell z := by
  refine ⟨nfUSqLiftHoleEscapeCollapse, nfUSqLiftHoleEscape_steps_to_collapse, ?_⟩
  exact nfUSqLiftHoleEscapeCollapse_not_in_UShell

def vATerm : Term V := vTerm.op A

def nfVA : NormalForm V :=
  ⟨vATerm, vA_normal⟩

private theorem nfUSqLiftHoleEscapeCollapse_steps_to_nfVA :
    NFStepR (α := V) R4 nfUSqLiftHoleEscapeCollapse nfVA := by
  refine ⟨RuleId.SqStable, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.hole, x, s, ?_, ?_⟩
    ·
      change uSqLiftHoleEscapeCollapseTerm
        = Ctx.plug Ctx.hole ((((x.op s).op (s.op s)).op s))
      simp [Ctx.plug, uSqLiftHoleEscapeCollapseTerm, vTerm, A, s, x]
    ·
      change vATerm = Ctx.plug Ctx.hole (((x.op s).op (s.op s)))
      simp [Ctx.plug, vATerm, vTerm, A, s, x]

private theorem nfVA_not_in_UShell :
    ¬ UShell nfVA := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    have hneq : vATerm ≠ uTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfU, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUHolePred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uSqLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUSqLiftHolePred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uSqLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUSqLiftAPred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uSqLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUSqLiftRightSPred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uStablePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUStablePred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uDecorHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUDecorHolePred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uDecorLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUDecorLiftHolePred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uDecorLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUDecorLiftAPred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uDecorLiftLeftSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUDecorLiftLeftSPred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uDecorLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUDecorLiftRightSPred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ uDecorRightPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfUDecorRightPred, vATerm] using congrArg Subtype.val h
  ·
    have hneq : vATerm ≠ mTerm := by
      native_decide
    exact hneq <| by
      simpa [nfVA, nfM, vATerm] using congrArg Subtype.val h

theorem exists_step_from_nfUSqLiftHoleEscapeCollapse_outside_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUSqLiftHoleEscapeCollapse z ∧ ¬ UShell z := by
  refine ⟨nfVA, nfUSqLiftHoleEscapeCollapse_steps_to_nfVA, ?_⟩
  exact nfVA_not_in_UShell

private theorem nfVA_steps_to_nfV :
    NFStepR (α := V) R4 nfVA nfV := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.hole, x, s, ?_, ?_⟩
    ·
      change vATerm = Ctx.plug Ctx.hole (((x.op s).op (s.op s)))
      simp [Ctx.plug, vATerm, vTerm, A, s, x]
    ·
      change vTerm = Ctx.plug Ctx.hole (x.op s)
      simp [Ctx.plug, vTerm, s, x]

private theorem nfV_not_in_UShell :
    ¬ UShell nfV := by
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    have hneq : vTerm ≠ uTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfU] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUHolePred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uSqLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUSqLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uSqLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUSqLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uSqLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUSqLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uStablePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUStablePred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uDecorHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUDecorHolePred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uDecorLiftHolePredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUDecorLiftHolePred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uDecorLiftAPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUDecorLiftAPred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uDecorLiftLeftSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUDecorLiftLeftSPred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uDecorLiftRightSPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUDecorLiftRightSPred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ uDecorRightPredTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfUDecorRightPred] using congrArg Subtype.val h
  ·
    have hneq : vTerm ≠ mTerm := by
      native_decide
    exact hneq <| by
      simpa [nfV, nfM] using congrArg Subtype.val h

theorem exists_step_from_nfVA_outside_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfVA z ∧ ¬ UShell z := by
  refine ⟨nfV, nfVA_steps_to_nfV, ?_⟩
  exact nfV_not_in_UShell

def VSpine (z : NormalForm V) : Prop :=
  z = nfUSqLiftHoleEscape ∨
  z = nfUSqLiftHoleEscapeCollapse ∨
  z = nfVA ∨
  z = nfV

theorem nfUSqLiftHolePred_reaches_VSpine :
    ∃ z : NormalForm V, NFStepR (α := V) R4 nfUSqLiftHolePred z ∧ VSpine z := by
  refine ⟨nfUSqLiftHoleEscape, ?_, ?_⟩
  · exact nfUSqLiftHolePred_steps_to_escape
  · exact Or.inl rfl

theorem nfUSqLiftHoleEscape_reaches_VSpine :
    ∃ z : NormalForm V, NFStepR (α := V) R4 nfUSqLiftHoleEscape z ∧ VSpine z := by
  refine ⟨nfUSqLiftHoleEscapeCollapse, ?_, ?_⟩
  · exact nfUSqLiftHoleEscape_steps_to_collapse
  · exact Or.inr (Or.inl rfl)

theorem nfUSqLiftHoleEscapeCollapse_reaches_VSpine :
    ∃ z : NormalForm V, NFStepR (α := V) R4 nfUSqLiftHoleEscapeCollapse z ∧ VSpine z := by
  refine ⟨nfVA, ?_, ?_⟩
  · exact nfUSqLiftHoleEscapeCollapse_steps_to_nfVA
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem nfVA_reaches_VSpine :
    ∃ z : NormalForm V, NFStepR (α := V) R4 nfVA z ∧ VSpine z := by
  refine ⟨nfV, ?_, ?_⟩
  · exact nfVA_steps_to_nfV
  · exact Or.inr (Or.inr (Or.inr rfl))

private theorem nfUDecorLiftHoleEscape_steps_to_nfUSqLiftHoleEscape :
    NFStepR (α := V) R4 nfUDecorLiftHoleEscape nfUSqLiftHoleEscape := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right vTerm (Ctx.right A Ctx.hole)) s, s, s, ?_, ?_⟩
    ·
      change uDecorLiftHoleEscapeTerm
        = Ctx.plug (Ctx.left (Ctx.right vTerm (Ctx.right A Ctx.hole)) s)
            (((s.op s).op (s.op s)))
      simp [Ctx.plug, uDecorLiftHoleEscapeTerm, vTerm, A, s, x]
    ·
      change uSqLiftHoleEscapeTerm
        = Ctx.plug (Ctx.left (Ctx.right vTerm (Ctx.right A Ctx.hole)) s)
            (s.op s)
      simp [Ctx.plug,  uSqLiftHoleEscapeTerm, vTerm, A, s, x]

theorem nfUDecorLiftHoleEscape_reaches_VSpine :
    ∃ z : NormalForm V, NFStepR (α := V) R4 nfUDecorLiftHoleEscape z ∧ VSpine z := by
  refine ⟨nfUSqLiftHoleEscape, nfUDecorLiftHoleEscape_steps_to_nfUSqLiftHoleEscape, ?_⟩
  exact Or.inl rfl

theorem exists_step_from_nfUDecorLiftHoleEscape_outside_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftHoleEscape z ∧ ¬ UShell z := by
  refine ⟨nfUSqLiftHoleEscape, nfUDecorLiftHoleEscape_steps_to_nfUSqLiftHoleEscape, ?_⟩
  exact nfUSqLiftHoleEscape_not_in_UShell

private theorem nfUDecorLiftAPredLeftEscape_steps_to_nfUSqLiftRightSPred :
    NFStepR (α := V) R4 nfUDecorLiftAPredLeftEscape nfUSqLiftRightSPred := by
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
    refine ⟨Ctx.left (Ctx.right x (Ctx.right s (Ctx.right s Ctx.hole))) s, x, x, ?_, ?_⟩
    ·
      change uDecorLiftAPredLeftEscapeTerm
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s (Ctx.right s Ctx.hole))) s)
            (((x.op x).op (x.op x)))
      simp [Ctx.plug, uDecorLiftAPredLeftEscapeTerm, A, s, x]
    ·
      change (x.op (s.op A)).op s
        = Ctx.plug (Ctx.left (Ctx.right x (Ctx.right s (Ctx.right s Ctx.hole))) s)
            (x.op x)
      simp [Ctx.plug, A, s, x]

theorem nfUDecorLiftAPredLeftEscape_reaches_UShell :
    ∃ z : NormalForm V, NFStepR (α := V) R4 nfUDecorLiftAPredLeftEscape z ∧ UShell z := by
  refine ⟨nfUSqLiftRightSPred, nfUDecorLiftAPredLeftEscape_steps_to_nfUSqLiftRightSPred, ?_⟩
  simp [UShell]

theorem exists_step_from_nfUDecorLiftAPredLeftEscape_into_UShell :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftAPredLeftEscape z ∧ UShell z := by
  exact nfUDecorLiftAPredLeftEscape_reaches_UShell

def ReenterShell (z : NormalForm V) : Prop :=
  ∃ w : NormalForm V, NFStepR (α := V) R4 z w ∧ UShell w

def ToVSpine (z : NormalForm V) : Prop :=
  ∃ w : NormalForm V, NFStepR (α := V) R4 z w ∧ VSpine w

def FlowsToShellOrVSpine (z : NormalForm V) : Prop :=
  ReenterShell z ∨ ToVSpine z

theorem nfUSqLiftHoleEscape_to_VSpine :
    ToVSpine nfUSqLiftHoleEscape := by
  refine ⟨nfUSqLiftHoleEscapeCollapse, ?_, ?_⟩
  · exact nfUSqLiftHoleEscape_steps_to_collapse
  · exact Or.inr (Or.inl rfl)

theorem nfUDecorLiftHoleEscape_to_VSpine :
    ToVSpine nfUDecorLiftHoleEscape := by
  refine ⟨nfUSqLiftHoleEscape, ?_, ?_⟩
  · exact nfUDecorLiftHoleEscape_steps_to_nfUSqLiftHoleEscape
  · exact Or.inl rfl

theorem nfUDecorLiftAPredLeftEscape_reenters :
    ReenterShell nfUDecorLiftAPredLeftEscape := by
  refine ⟨nfUSqLiftRightSPred, ?_, ?_⟩
  · exact nfUDecorLiftAPredLeftEscape_steps_to_nfUSqLiftRightSPred
  · simp [UShell]

theorem nfUSqLiftHoleEscape_to_VSpine' :
    ToVSpine nfUSqLiftHoleEscape := by
  refine ⟨nfUSqLiftHoleEscapeCollapse, ?_, ?_⟩
  · exact nfUSqLiftHoleEscape_steps_to_collapse
  · exact Or.inr (Or.inl rfl)

theorem nfUDecorLiftHoleEscape_to_VSpine' :
    ToVSpine nfUDecorLiftHoleEscape := by
  refine ⟨nfUSqLiftHoleEscape, ?_, ?_⟩
  · exact nfUDecorLiftHoleEscape_steps_to_nfUSqLiftHoleEscape
  · exact Or.inl rfl

theorem nfUSqLiftHoleEscapeCollapse_to_VSpine :
    ToVSpine nfUSqLiftHoleEscapeCollapse := by
  refine ⟨nfVA, ?_, ?_⟩
  · exact nfUSqLiftHoleEscapeCollapse_steps_to_nfVA
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem nfVA_to_VSpine :
    ToVSpine nfVA := by
  refine ⟨nfV, ?_, ?_⟩
  · exact nfVA_steps_to_nfV
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem nfUSqLiftHolePred_has_escape_to_VSpine :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUSqLiftHolePred z ∧
      ¬ UShell z ∧
      ToVSpine z := by
  refine ⟨nfUSqLiftHoleEscape, ?_, ?_, ?_⟩
  · exact nfUSqLiftHolePred_steps_to_escape
  · exact nfUSqLiftHoleEscape_not_in_UShell
  · exact nfUSqLiftHoleEscape_to_VSpine'

theorem nfUDecorLiftHolePred_has_escape_to_VSpine :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftHolePred z ∧
      ¬ UShell z ∧
      ToVSpine z := by
  refine ⟨nfUDecorLiftHoleEscape, ?_, ?_, ?_⟩
  · exact nfUDecorLiftHolePred_steps_to_escape
  · exact nfUDecorLiftHoleEscape_not_in_UShell
  · exact nfUDecorLiftHoleEscape_to_VSpine'

theorem nfUDecorLiftAPred_has_escape_that_reenters :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftAPred z ∧
      ¬ UShell z ∧
      ReenterShell z := by
  refine ⟨nfUDecorLiftAPredLeftEscape, ?_, ?_, ?_⟩
  · exact nfUDecorLiftAPred_steps_to_left_escape
  · exact nfUDecorLiftAPredLeftEscape_not_in_UShell
  · exact nfUDecorLiftAPredLeftEscape_reenters

theorem nfUSqLiftHoleEscape_flows :
    FlowsToShellOrVSpine nfUSqLiftHoleEscape := by
  exact Or.inr nfUSqLiftHoleEscape_to_VSpine'

theorem nfUDecorLiftHoleEscape_flows :
    FlowsToShellOrVSpine nfUDecorLiftHoleEscape := by
  exact Or.inr nfUDecorLiftHoleEscape_to_VSpine'

theorem nfUDecorLiftAPredLeftEscape_flows :
    FlowsToShellOrVSpine nfUDecorLiftAPredLeftEscape := by
  exact Or.inl nfUDecorLiftAPredLeftEscape_reenters

def FirstShellBehavior (z : NormalForm V) : Prop :=
  UShell z ∨ ReenterShell z ∨ ToVSpine z

theorem nfUSqLiftHolePred_breaks_to_VSpine :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUSqLiftHolePred z ∧
      ¬ UShell z ∧
      ToVSpine z := by
  exact nfUSqLiftHolePred_has_escape_to_VSpine

theorem nfUDecorLiftHolePred_breaks_to_VSpine :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftHolePred z ∧
      ¬ UShell z ∧
      ToVSpine z := by
  exact nfUDecorLiftHolePred_has_escape_to_VSpine

theorem nfUDecorLiftAPred_breaks_and_reenters :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftAPred z ∧
      ¬ UShell z ∧
      ReenterShell z := by
  exact nfUDecorLiftAPred_has_escape_that_reenters

theorem NFStepR_from_nfUDecorLiftLeftSPred_in_UShell {z : NormalForm V} :
    NFStepR (α := V) R4 nfUDecorLiftLeftSPred z → UShell z := by
  intro h
  rw [NFStepR_from_nfUDecorLiftLeftSPred_eq_nfU (z := z) h]
  simp [UShell]


def SettledInwardPoint (u : NormalForm V) : Prop :=
  u = nfU ∨
  u = nfUHolePred ∨
  u = nfUStablePred ∨
  u = nfUDecorHolePred ∨
  u = nfUDecorRightPred ∨
  u = nfUSqLiftAPred ∨
  u = nfUSqLiftRightSPred ∨
  u = nfUDecorLiftLeftSPred ∨
  u = nfUDecorLiftRightSPred ∨
  u = nfM

private theorem SettledInwardPoint_step_in_UShell {u v : NormalForm V} :
    SettledInwardPoint u →
    NFStepR (α := V) R4 u v →
    UShell v := by
  intro hu hstep
  rcases hu with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact UShell_of_NFStepR_from_nfU (z := v) hstep
  · exact NFStepR_from_nfUHolePred_in_UShell (z := v) hstep
  · exact NFStepR_from_nfUStablePred_in_UShell (z := v) hstep
  · exact NFStepR_from_nfUDecorHolePred_in_UShell (z := v) hstep
  · exact NFStepR_from_nfUDecorRightPred_in_UShell (z := v) hstep
  · exact NFStepR_from_nfUSqLiftAPred_in_UShell (z := v) hstep
  · exact NFStepR_from_nfUSqLiftRightSPred_in_UShell (z := v) hstep
  · exact NFStepR_from_nfUDecorLiftLeftSPred_in_UShell (z := v) hstep
  · exact NFStepR_from_nfUDecorLiftRightSPred_in_UShell (z := v) hstep
  · exact False.elim (no_NFStepR_from_nfM (z := v) hstep)

def ShellBreakerPoint (u : NormalForm V) : Prop :=
  u = nfUSqLiftHolePred ∨
  u = nfUDecorLiftHolePred ∨
  u = nfUDecorLiftAPred

theorem ShellBreakerPoint_behavior {u : NormalForm V} :
    ShellBreakerPoint u →
    (∃ z : NormalForm V, NFStepR (α := V) R4 u z ∧ ¬ UShell z ∧ FlowsToShellOrVSpine z) := by
  intro hu
  rcases hu with rfl | rfl | rfl
  ·
    refine ⟨nfUSqLiftHoleEscape, ?_, ?_, ?_⟩
    · exact nfUSqLiftHolePred_steps_to_escape
    · exact nfUSqLiftHoleEscape_not_in_UShell
    · exact nfUSqLiftHoleEscape_flows
  ·
    refine ⟨nfUDecorLiftHoleEscape, ?_, ?_, ?_⟩
    · exact nfUDecorLiftHolePred_steps_to_escape
    · exact nfUDecorLiftHoleEscape_not_in_UShell
    · exact nfUDecorLiftHoleEscape_flows
  ·
    refine ⟨nfUDecorLiftAPredLeftEscape, ?_, ?_, ?_⟩
    · exact nfUDecorLiftAPred_steps_to_left_escape
    · exact nfUDecorLiftAPredLeftEscape_not_in_UShell
    · exact nfUDecorLiftAPredLeftEscape_flows

def FirstShellPoint (u : NormalForm V) : Prop :=
  u = nfUHolePred ∨
  u = nfUSqLiftHolePred ∨
  u = nfUSqLiftAPred ∨
  u = nfUSqLiftRightSPred ∨
  u = nfUStablePred ∨
  u = nfUDecorHolePred ∨
  u = nfUDecorLiftHolePred ∨
  u = nfUDecorLiftAPred ∨
  u = nfUDecorLiftLeftSPred ∨
  u = nfUDecorLiftRightSPred ∨
  u = nfUDecorRightPred

theorem FirstShellPoint_partition {u : NormalForm V} :
    FirstShellPoint u →
    SettledInwardPoint u ∨ ShellBreakerPoint u := by
  intro hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [SettledInwardPoint, ShellBreakerPoint]

theorem FirstShellPoint_in_UShell {u : NormalForm V} :
    FirstShellPoint u → UShell u := by
  intro hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [UShell]

theorem FirstShellPoint_behavior {u : NormalForm V} :
    FirstShellPoint u → FirstShellBehavior u := by
  intro hu
  exact Or.inl (FirstShellPoint_in_UShell hu)

def FirstShellFlowBehavior (u : NormalForm V) : Prop :=
  SettledInwardPoint u ∨
  ∃ z : NormalForm V,
    NFStepR (α := V) R4 u z ∧
    ¬ UShell z ∧
    FlowsToShellOrVSpine z

theorem FirstShellPoint_flowBehavior {u : NormalForm V} :
    FirstShellPoint u → FirstShellFlowBehavior u := by
  intro hu
  rcases FirstShellPoint_partition hu with hIn | hBr
  · exact Or.inl hIn
  · exact Or.inr (ShellBreakerPoint_behavior hBr)

theorem NFAdjR_at_nfU_firstShell {u : NormalForm V} :
    NFAdjR (α := V) R4 nfU u → FirstShellPoint u := by
  intro h
  rcases (NFAdjR_at_nfU_iff (z := u)).1 h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FirstShellPoint]

theorem NFAdjR_at_nfU_flowBehavior {u : NormalForm V} :
    NFAdjR (α := V) R4 nfU u → FirstShellFlowBehavior u := by
  intro h
  exact FirstShellPoint_flowBehavior (NFAdjR_at_nfU_firstShell (u := u) h)

def InternalVSpinePoint (z : NormalForm V) : Prop :=
  z = nfUSqLiftHoleEscape ∨
  z = nfUSqLiftHoleEscapeCollapse ∨
  z = nfVA

theorem VSpine_partition {z : NormalForm V} :
    VSpine z → InternalVSpinePoint z ∨ z = nfV := by
  intro hz
  rcases hz with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr h))
  · exact Or.inr h

theorem InternalVSpinePoint_reaches_VSpine {z : NormalForm V} :
    InternalVSpinePoint z →
    ∃ w : NormalForm V, NFStepR (α := V) R4 z w ∧ VSpine w := by
  intro hz
  rcases hz with h | h | h
  ·
    rw [h]
    exact nfUSqLiftHoleEscape_reaches_VSpine
  ·
    rw [h]
    exact nfUSqLiftHoleEscapeCollapse_reaches_VSpine
  ·
    rw [h]
    exact nfVA_reaches_VSpine

theorem VSpine_terminal_behavior {z : NormalForm V} :
    VSpine z →
      z = nfV ∨ ∃ w : NormalForm V, NFStepR (α := V) R4 z w ∧ VSpine w := by
  intro hz
  rcases VSpine_partition hz with hInt | hV
  ·
    right
    exact InternalVSpinePoint_reaches_VSpine hInt
  ·
    left
    exact hV

theorem nfV_terminal {z : NormalForm V} :
    ¬ NFStepR (α := V) R4 nfV z := by
  exact no_NFStepR_from_nfV (z := z)

theorem VSpine_nfV_no_successor {z : NormalForm V} :
    z = nfV → ¬ ∃ w : NormalForm V, NFStepR (α := V) R4 z w := by
  intro hz
  subst hz
  intro h
  rcases h with ⟨w, hw⟩
  exact no_NFStepR_from_nfV (z := w) hw

theorem nfUSqLiftHolePred_flows_to_terminal_VSpine :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUSqLiftHolePred z ∧
      ¬ UShell z ∧
      ToVSpine z := by
  exact nfUSqLiftHolePred_has_escape_to_VSpine

theorem nfUDecorLiftHolePred_flows_to_terminal_VSpine :
    ∃ z : NormalForm V,
      NFStepR (α := V) R4 nfUDecorLiftHolePred z ∧
      ¬ UShell z ∧
      ToVSpine z := by
  exact nfUDecorLiftHolePred_has_escape_to_VSpine

theorem NFEqR_R4_nfU_nfV :
    NFEqR (α := V) R4 nfU nfV := by
  have hPredU :
      NFEqR (α := V) R4 nfUSqLiftHolePred nfU := by
    exact EqvGen.rel' nfUSqLiftHolePred_steps_to_nfU

  have hPredEsc :
      NFEqR (α := V) R4 nfUSqLiftHolePred nfUSqLiftHoleEscape := by
    exact EqvGen.rel' nfUSqLiftHolePred_steps_to_escape

  have hEscCol :
      NFEqR (α := V) R4 nfUSqLiftHoleEscape nfUSqLiftHoleEscapeCollapse := by
    exact EqvGen.rel' nfUSqLiftHoleEscape_steps_to_collapse

  have hColVA :
      NFEqR (α := V) R4 nfUSqLiftHoleEscapeCollapse nfVA := by
    exact EqvGen.rel' nfUSqLiftHoleEscapeCollapse_steps_to_nfVA

  have hVAV :
      NFEqR (α := V) R4 nfVA nfV := by
    exact EqvGen.rel' nfVA_steps_to_nfV

  exact
    EqvGen.trans'
      (EqvGen.symm' hPredU)
      (EqvGen.trans' hPredEsc
        (EqvGen.trans' hEscCol
          (EqvGen.trans' hColVA hVAV)))

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
