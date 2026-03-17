import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_Spine

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

section ExactNode

inductive ExactLeaf where
  | xa
  | u
  | m
  | v
  deriving DecidableEq, Repr

inductive ExactNode where
  | core (tg : CoreKernelTarget)
  | leaf (ℓ : ExactLeaf)
  deriving DecidableEq, Repr

def exactLeafNF : ExactLeaf → NormalForm V
  | .xa => nfXA
  | .u  => nfU
  | .m  => nfM
  | .v  => nfV

def exactNodeNF : ExactNode → NormalForm V
  | .core tg => coreNFOfTarget tg
  | .leaf ℓ  => exactLeafNF ℓ

inductive ExactChildren where
  | zero
  | one (a : ExactNode)
  | two (a b : ExactNode)
  deriving DecidableEq, Repr

def ExactChildren.Mem : ExactChildren → ExactNode → Prop
  | .zero, _    => False
  | .one a, x   => x = a
  | .two a b, x => x = a ∨ x = b

instance : Membership ExactNode ExactChildren where
  mem := ExactChildren.Mem

def exactOneStepChildrenR4 : ExactNode → ExactChildren
  | .leaf .xa                      => .one (.leaf .v)
  | .leaf .u                       => .zero
  | .leaf .m                       => .zero
  | .leaf .v                       => .zero
  | .core .nfXASqRightPred         => .one (.leaf .xa)
  | .core .nfUSqLiftRightSPred     => .one (.leaf .u)
  | .core .nfXADecorRightPred      => .one (.leaf .xa)
  | .core .nfUDecorLiftRightSPred  => .one (.leaf .u)
  | .core .nfXADecorLeftPred       => .one (.leaf .xa)
  | .core .nfUDecorLiftLeftSPred   => .one (.leaf .u)
  | .core .nfUStablePred           => .one (.leaf .u)
  | .core .nfUHolePred             => .one (.leaf .u)
  | .core .nfUDecorHolePred        => .two (.leaf .u) (.core .nfUHolePred)
  | .core .nfXASqAPred             => .two (.leaf .xa) (.core .nfXASqRightPred)
  | .core .nfUSqLiftAPred          => .two (.leaf .u) (.core .nfUSqLiftRightSPred)
  | .core .nfUDecorRightPred       => .two (.leaf .u) (.leaf .m)

@[simp] theorem mem_zero (x : ExactNode) :
    x ∈ ExactChildren.zero ↔ False := Iff.rfl

@[simp] theorem mem_one (x a : ExactNode) :
    x ∈ ExactChildren.one a ↔ x = a := Iff.rfl

@[simp] theorem mem_two (x a b : ExactNode) :
    x ∈ ExactChildren.two a b ↔ x = a ∨ x = b := Iff.rfl

@[simp] theorem exact_children_nfXASqRightPred :
    exactOneStepChildrenR4 (.core .nfXASqRightPred) = .one (.leaf .xa) := rfl

@[simp] theorem exact_children_nfUDecorHolePred :
    exactOneStepChildrenR4 (.core .nfUDecorHolePred)
      = .two (.leaf .u) (.core .nfUHolePred) := rfl

@[simp] theorem exact_children_leaf_xa :
    exactOneStepChildrenR4 (.leaf .xa) = .one (.leaf .v) := rfl

theorem one_step_target_mem_exactChildren
    {tg : CoreKernelTarget} {z : NormalForm V}
    (h : NFStepR (α := V) R4 (coreNFOfTarget tg) z) :
    ∃ n : ExactNode,
      z = exactNodeNF n ∧ n ∈ exactOneStepChildrenR4 (.core tg) := by
  cases tg with
  | nfXASqRightPred =>
      have hz : z = nfXA :=
        (targetKernelEnvelope_of_target .nfXASqRightPred) h
      refine ⟨.leaf .xa, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfUSqLiftRightSPred =>
      have hz : z = nfU :=
        (targetKernelEnvelope_of_target .nfUSqLiftRightSPred) h
      refine ⟨.leaf .u, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfXADecorRightPred =>
      have hz : z = nfXA :=
        (targetKernelEnvelope_of_target .nfXADecorRightPred) h
      refine ⟨.leaf .xa, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfUDecorLiftRightSPred =>
      have hz : z = nfU :=
        (targetKernelEnvelope_of_target .nfUDecorLiftRightSPred) h
      refine ⟨.leaf .u, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfXADecorLeftPred =>
      have hz : z = nfXA :=
        (targetKernelEnvelope_of_target .nfXADecorLeftPred) h
      refine ⟨.leaf .xa, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfUDecorLiftLeftSPred =>
      have hz : z = nfU :=
        (targetKernelEnvelope_of_target .nfUDecorLiftLeftSPred) h
      refine ⟨.leaf .u, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfUStablePred =>
      have hz : z = nfU :=
        (targetKernelEnvelope_of_target .nfUStablePred) h
      refine ⟨.leaf .u, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfUHolePred =>
      have hz : z = nfU :=
        (targetKernelEnvelope_of_target .nfUHolePred) h
      refine ⟨.leaf .u, ?_, ?_⟩
      · simpa [exactNodeNF, exactLeafNF] using hz
      · simp [exactOneStepChildrenR4]

  | nfUDecorHolePred =>
      have hz : z = nfU ∨ z = nfUHolePred :=
        (targetKernelEnvelope_of_target .nfUDecorHolePred) h
      rcases hz with hz | hz
      · refine ⟨.leaf .u, ?_, ?_⟩
        · simpa [exactNodeNF, exactLeafNF] using hz
        · simp [exactOneStepChildrenR4]
      · refine ⟨.core .nfUHolePred, ?_, ?_⟩
        · change z = coreNFOfTarget .nfUHolePred
          simpa using hz
        · simp [exactOneStepChildrenR4]

  | nfXASqAPred =>
      have hz : z = nfXA ∨ z = nfXASqRightPred :=
        (targetKernelEnvelope_of_target .nfXASqAPred) h
      rcases hz with hz | hz
      · refine ⟨.leaf .xa, ?_, ?_⟩
        · simpa [exactNodeNF, exactLeafNF] using hz
        · simp [exactOneStepChildrenR4]
      · refine ⟨.core .nfXASqRightPred, ?_, ?_⟩
        · change z = coreNFOfTarget .nfXASqRightPred
          simpa using hz
        · simp [exactOneStepChildrenR4]

  | nfUSqLiftAPred =>
      have hz : z = nfU ∨ z = nfUSqLiftRightSPred :=
        (targetKernelEnvelope_of_target .nfUSqLiftAPred) h
      rcases hz with hz | hz
      · refine ⟨.leaf .u, ?_, ?_⟩
        · simpa [exactNodeNF, exactLeafNF] using hz
        · simp [exactOneStepChildrenR4]
      · refine ⟨.core .nfUSqLiftRightSPred, ?_, ?_⟩
        · change z = coreNFOfTarget .nfUSqLiftRightSPred
          simpa using hz
        · simp [exactOneStepChildrenR4]

  | nfUDecorRightPred =>
      have hz : z = nfU ∨ z = nfM :=
        (targetKernelEnvelope_of_target .nfUDecorRightPred) h
      rcases hz with hz | hz
      · refine ⟨.leaf .u, ?_, ?_⟩
        · simpa [exactNodeNF, exactLeafNF] using hz
        · simp [exactOneStepChildrenR4]
      · refine ⟨.leaf .m, ?_, ?_⟩
        · simpa [exactNodeNF, exactLeafNF] using hz
        · simp [exactOneStepChildrenR4]

def OneStepProxyR4 (src dst : ExactNode) : Prop :=
  dst ∈ exactOneStepChildrenR4 src

theorem nfStepR_core_to_proxy
    {tg : CoreKernelTarget} {z : NormalForm V}
    (h : NFStepR (α := V) R4 (coreNFOfTarget tg) z) :
    ∃ dst : ExactNode, OneStepProxyR4 (.core tg) dst ∧ z = exactNodeNF dst := by
  rcases one_step_target_mem_exactChildren h with ⟨dst, hz, hmem⟩
  exact ⟨dst, hmem, hz⟩

@[simp] theorem proxy_leaf_xa_iff (dst : ExactNode) :
    OneStepProxyR4 (.leaf .xa) dst ↔ dst = .leaf .v := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem not_proxy_from_leaf_u (dst : ExactNode) :
    ¬ OneStepProxyR4 (.leaf .u) dst := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem not_proxy_from_leaf_m (dst : ExactNode) :
    ¬ OneStepProxyR4 (.leaf .m) dst := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem not_proxy_from_leaf_v (dst : ExactNode) :
    ¬ OneStepProxyR4 (.leaf .v) dst := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfXASqRightPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfXASqRightPred) dst ↔ dst = .leaf .xa := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUSqLiftRightSPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUSqLiftRightSPred) dst ↔ dst = .leaf .u := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUDecorHolePred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUDecorHolePred) dst
      ↔ dst = .leaf .u ∨ dst = .core .nfUHolePred := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfXASqAPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfXASqAPred) dst
      ↔ dst = .leaf .xa ∨ dst = .core .nfXASqRightPred := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUSqLiftAPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUSqLiftAPred) dst
      ↔ dst = .leaf .u ∨ dst = .core .nfUSqLiftRightSPred := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUDecorRightPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUDecorRightPred) dst
      ↔ dst = .leaf .u ∨ dst = .leaf .m := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

private theorem normalForm_ne_of_val_ne {a b : NormalForm V}
    (h : a.1 ≠ b.1) : a ≠ b := by
  intro hab
  apply h
  exact congrArg Subtype.val hab

theorem proxy_nfXASqAPred_no_collision :
    exactNodeNF (.leaf .xa) ≠ exactNodeNF (.core .nfXASqRightPred) := by
  apply normalForm_ne_of_val_ne
  change xATerm ≠ xASqRightSPredTerm
  intro h
  simp [xATerm, xASqRightSPredTerm, x, s, A] at h

theorem proxy_nfUDecorHolePred_no_collision :
    exactNodeNF (.leaf .u) ≠ exactNodeNF (.core .nfUHolePred) := by
  apply normalForm_ne_of_val_ne
  change uTerm ≠ uHolePredTerm
  intro h
  simp [uTerm, uHolePredTerm, x, s, A] at h

theorem proxy_nfUDecorRightPred_no_collision :
    exactNodeNF (.leaf .u) ≠ exactNodeNF (.leaf .m) := by
  apply normalForm_ne_of_val_ne
  change uTerm ≠ mTerm
  intro h
  simp [uTerm, mTerm, x, s, A] at h

theorem proxy_nfUSqLiftAPred_no_collision :
    exactNodeNF (.leaf .u) ≠ exactNodeNF (.core .nfUSqLiftRightSPred) := by
  intro h
  have hEq : nfU = nfUSqLiftRightSPred := by
    simpa [exactNodeNF, exactLeafNF, coreNFOfTarget] using h
  have hself : NFStepR (α := V) R4 nfU nfU := by
    simpa [hEq] using nfUSqLiftRightSPred_steps_to_nfU
  exact no_NFStepR_from_nfU (z := nfU) hself

theorem proxy_nfXASqAPred_unique
    {a b : ExactNode}
    (ha : OneStepProxyR4 (.core .nfXASqAPred) a)
    (hb : OneStepProxyR4 (.core .nfXASqAPred) b)
    (hEq : exactNodeNF a = exactNodeNF b) :
    a = b := by
  rcases (proxy_nfXASqAPred_iff a).mp ha with ha | ha
  · rcases (proxy_nfXASqAPred_iff b).mp hb with hb | hb
    · subst ha; subst hb; rfl
    · subst ha; subst hb
      exfalso
      exact proxy_nfXASqAPred_no_collision hEq
  · rcases (proxy_nfXASqAPred_iff b).mp hb with hb | hb
    · subst ha; subst hb
      exfalso
      exact proxy_nfXASqAPred_no_collision hEq.symm
    · subst ha; subst hb; rfl

theorem proxy_nfUDecorHolePred_unique
    {a b : ExactNode}
    (ha : OneStepProxyR4 (.core .nfUDecorHolePred) a)
    (hb : OneStepProxyR4 (.core .nfUDecorHolePred) b)
    (hEq : exactNodeNF a = exactNodeNF b) :
    a = b := by
  rcases (proxy_nfUDecorHolePred_iff a).mp ha with ha | ha
  · rcases (proxy_nfUDecorHolePred_iff b).mp hb with hb | hb
    · subst ha; subst hb; rfl
    · subst ha; subst hb
      exfalso
      exact proxy_nfUDecorHolePred_no_collision hEq
  · rcases (proxy_nfUDecorHolePred_iff b).mp hb with hb | hb
    · subst ha; subst hb
      exfalso
      exact proxy_nfUDecorHolePred_no_collision hEq.symm
    · subst ha; subst hb; rfl

theorem proxy_nfUDecorRightPred_unique
    {a b : ExactNode}
    (ha : OneStepProxyR4 (.core .nfUDecorRightPred) a)
    (hb : OneStepProxyR4 (.core .nfUDecorRightPred) b)
    (hEq : exactNodeNF a = exactNodeNF b) :
    a = b := by
  rcases (proxy_nfUDecorRightPred_iff a).mp ha with ha | ha
  · rcases (proxy_nfUDecorRightPred_iff b).mp hb with hb | hb
    · subst ha; subst hb; rfl
    · subst ha; subst hb
      exfalso
      exact proxy_nfUDecorRightPred_no_collision hEq
  · rcases (proxy_nfUDecorRightPred_iff b).mp hb with hb | hb
    · subst ha; subst hb
      exfalso
      exact proxy_nfUDecorRightPred_no_collision hEq.symm
    · subst ha; subst hb; rfl


theorem proxy_nfUSqLiftAPred_unique
    {a b : ExactNode}
    (ha : OneStepProxyR4 (.core .nfUSqLiftAPred) a)
    (hb : OneStepProxyR4 (.core .nfUSqLiftAPred) b)
    (hEq : exactNodeNF a = exactNodeNF b) :
    a = b := by
  rcases (proxy_nfUSqLiftAPred_iff a).mp ha with ha | ha
  · rcases (proxy_nfUSqLiftAPred_iff b).mp hb with hb | hb
    · subst ha; subst hb; rfl
    · subst ha; subst hb
      exfalso
      exact proxy_nfUSqLiftAPred_no_collision hEq
  · rcases (proxy_nfUSqLiftAPred_iff b).mp hb with hb | hb
    · subst ha; subst hb
      exfalso
      exact proxy_nfUSqLiftAPred_no_collision hEq.symm
    · subst ha; subst hb; rfl


@[simp] theorem exactNodeNF_core (tg : CoreKernelTarget) :
    exactNodeNF (.core tg) = coreNFOfTarget tg := rfl

@[simp] theorem exactNodeNF_leaf_xa :
    exactNodeNF (.leaf .xa) = nfXA := rfl

@[simp] theorem exactNodeNF_leaf_u :
    exactNodeNF (.leaf .u) = nfU := rfl

@[simp] theorem exactNodeNF_leaf_m :
    exactNodeNF (.leaf .m) = nfM := rfl

@[simp] theorem exactNodeNF_leaf_v :
    exactNodeNF (.leaf .v) = nfV := rfl

private theorem nfUSqLiftAPred_steps_to_nfUSqLiftRightSPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUSqLiftAPred))
      (exactNodeNF (.core .nfUSqLiftRightSPred)) := by
  change NFStepR (α := V) R4 nfUSqLiftAPred nfUSqLiftRightSPred
  refine ⟨RuleId.SqAbsorb, ?_, ?_⟩
  · simp [R4]
  ·
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



private theorem nfXASqAPred_steps_to_nfXA :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfXASqAPred))
      (exactNodeNF (.leaf .xa)) := by
  change NFStepR (α := V) R4 nfXASqAPred nfXA
  refine ⟨RuleId.SqAbsorb, by simp [R4], ?_⟩
  refine ⟨Ctx.right x Ctx.hole, s, s, ?_, ?_⟩
  ·
    change xASqAPredTerm = Ctx.plug (Ctx.right x Ctx.hole) (((s.op s).op (s.op s)))
    simp [Ctx.plug, xASqAPredTerm, A, s, x]
  ·
    change xATerm = Ctx.plug (Ctx.right x Ctx.hole) (s.op s)
    simp [Ctx.plug, xATerm, A, s, x]

private theorem nfXASqAPred_steps_to_nfXASqRightPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfXASqAPred))
      (exactNodeNF (.core .nfXASqRightPred)) := by
  change NFStepR (α := V) R4 nfXASqAPred nfXASqRightPred
  refine ⟨RuleId.SqAbsorb, by simp [R4], ?_⟩
  refine ⟨Ctx.right x (Ctx.left Ctx.hole A), x, x, ?_, ?_⟩
  ·
    change xASqAPredTerm = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole A)) (((x.op x).op (x.op x)))
    simp [Ctx.plug, xASqAPredTerm, A, s, x]
  ·
    change xASqRightSPredTerm = Ctx.plug (Ctx.right x (Ctx.left Ctx.hole A)) (x.op x)
    simp [Ctx.plug, xASqRightSPredTerm, A, s, x]


theorem proxy_realizes_nfU_from_nfUSqLiftAPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUSqLiftAPred))
      (exactNodeNF (.leaf .u)) := by
  simpa [exactNodeNF, exactLeafNF]
    using nfUSqLiftAPred_steps_to_nfU

theorem proxy_realizes_nfUSqLiftRightPred_from_nfUSqLiftAPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUSqLiftAPred))
      (exactNodeNF (.core .nfUSqLiftRightSPred)) := by
  simpa [exactNodeNF]
    using nfUSqLiftAPred_steps_to_nfUSqLiftRightSPred

theorem proxy_realizes_nfXA_from_nfXASqAPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfXASqAPred))
      (exactNodeNF (.leaf .xa)) := by
  exact nfXASqAPred_steps_to_nfXA

theorem proxy_realizes_nfXASqRightPred_from_nfXASqAPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfXASqAPred))
      (exactNodeNF (.core .nfXASqRightPred)) := by
  exact nfXASqAPred_steps_to_nfXASqRightPred

theorem proxy_realizes_nfU_from_nfUDecorHolePred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUDecorHolePred))
      (exactNodeNF (.leaf .u)) := by
  simpa [exactNodeNF, exactLeafNF]
    using nfUDecorHolePred_steps_to_nfU

theorem proxy_realizes_nfUHolePred_from_nfUDecorHolePred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUDecorHolePred))
      (exactNodeNF (.core .nfUHolePred)) := by
  simpa [exactNodeNF]
    using nfUDecorHolePred_steps_to_nfUHolePred

theorem proxy_realizes_nfU_from_nfUDecorRightPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUDecorRightPred))
      (exactNodeNF (.leaf .u)) := by
  simpa [exactNodeNF, exactLeafNF]
    using nfUDecorRightPred_steps_to_nfU

theorem proxy_realizes_nfM_from_nfUDecorRightPred :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUDecorRightPred))
      (exactNodeNF (.leaf .m)) := by
  simpa [exactNodeNF, exactLeafNF]
    using nfUDecorRightPred_steps_to_nfM

theorem proxy_exact_nfXASqAPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfXASqAPred)) z
      ↔ z = exactNodeNF (.leaf .xa)
       ∨ z = exactNodeNF (.core .nfXASqRightPred) := by
  constructor
  · intro hz
    rcases one_step_target_mem_exactChildren (tg := .nfXASqAPred) hz with
      ⟨n, rfl, hn⟩
    rcases (proxy_nfXASqAPred_iff n).mp hn with hn | hn
    · left
      simp [hn]
    · right
      simp [hn]
  · intro hz
    rcases hz with rfl | rfl
    · exact proxy_realizes_nfXA_from_nfXASqAPred
    · exact proxy_realizes_nfXASqRightPred_from_nfXASqAPred

--nfUSqLiftAPred、nfUDecorHolePred、nfUDecorRightPred

theorem proxy_exact_nfUSqLiftAPred
    {z : NormalForm V} :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUSqLiftAPred)) z
    ↔ z = exactNodeNF (.leaf .u)
      ∨ z = exactNodeNF (.core .nfUSqLiftRightSPred) := by
  constructor
  · intro hz
    rcases one_step_target_mem_exactChildren (tg := .nfUSqLiftAPred) hz with
      ⟨n, hzEq, hn⟩
    rcases (proxy_nfUSqLiftAPred_iff n).mp hn with hn | hn
    · left
      simpa [hn] using hzEq
    · right
      simpa [hn] using hzEq
  · intro hz
    rcases hz with rfl | rfl
    ·
      simpa [exactNodeNF, exactLeafNF] using
        (nfUSqLiftAPred_steps_to_nfU : NFStepR (α := V) R4 nfUSqLiftAPred nfU)
    ·
      exact nfUSqLiftAPred_steps_to_nfUSqLiftRightSPred

--theorem proxy_exact_nfUDecorHolePred
theorem proxy_exact_nfUDecorHolePred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfUDecorHolePred)) z
      ↔ z = exactNodeNF (.leaf .u)
       ∨ z = exactNodeNF (.core .nfUHolePred) := by
  constructor
  · intro hz
    rcases one_step_target_mem_exactChildren (tg := .nfUDecorHolePred) hz with
      ⟨n, rfl, hn⟩
    rcases (proxy_nfUDecorHolePred_iff n).mp hn with hn | hn
    · left
      simp [hn]
    · right
      simp [hn]
  · intro hz
    rcases hz with rfl | rfl
    · exact proxy_realizes_nfU_from_nfUDecorHolePred
    · exact proxy_realizes_nfUHolePred_from_nfUDecorHolePred

theorem proxy_exact_nfUDecorRightPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfUDecorRightPred)) z
      ↔ z = exactNodeNF (.leaf .u)
       ∨ z = exactNodeNF (.leaf .m) := by
  constructor
  · intro hz
    rcases one_step_target_mem_exactChildren (tg := .nfUDecorRightPred) hz with
      ⟨n, rfl, hn⟩
    rcases (proxy_nfUDecorRightPred_iff n).mp hn with hn | hn
    · left
      simp [hn]
    · right
      simp [hn]
  · intro hz
    rcases hz with rfl | rfl
    · exact proxy_realizes_nfU_from_nfUDecorRightPred
    · exact proxy_realizes_nfM_from_nfUDecorRightPred

@[simp] theorem proxy_nfXADecorRightPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfXADecorRightPred) dst ↔ dst = .leaf .xa := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUDecorLiftRightSPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUDecorLiftRightSPred) dst ↔ dst = .leaf .u := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfXADecorLeftPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfXADecorLeftPred) dst ↔ dst = .leaf .xa := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUDecorLiftLeftSPred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUDecorLiftLeftSPred) dst ↔ dst = .leaf .u := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUStablePred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUStablePred) dst ↔ dst = .leaf .u := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

@[simp] theorem proxy_nfUHolePred_iff (dst : ExactNode) :
    OneStepProxyR4 (.core .nfUHolePred) dst ↔ dst = .leaf .u := by
  simp [OneStepProxyR4, exactOneStepChildrenR4]

/-既に定義されています。
private theorem nfUHolePred_steps_to_nfU :
    NFStepR (α := V) R4
      (exactNodeNF (.core .nfUHolePred))
      (exactNodeNF (.leaf .u)) := by
  change NFStepR (α := V) R4 nfUHolePred nfU
  refine ⟨RuleId.SqAbsorb, by simp [R4], ?_⟩
  refine ⟨Ctx.hole, xATerm, s, ?_, ?_⟩
  ·
    change uHolePredTerm = (((xATerm.op s).op (s.op s)))
    simp [uHolePredTerm, uTerm, xATerm, A, s, x]
  ·
    change uTerm = (xATerm.op s)
    simp [uTerm, xATerm, A, s, x]
-/

private theorem proxy_exact_of_singleton
    {tg : CoreKernelTarget} {dst : ExactNode} {z : NormalForm V}
    (hiff : ∀ n : ExactNode, OneStepProxyR4 (.core tg) n ↔ n = dst)
    (hstep : NFStepR (α := V) R4 (exactNodeNF (.core tg)) (exactNodeNF dst)) :
    NFStepR (α := V) R4 (exactNodeNF (.core tg)) z ↔ z = exactNodeNF dst := by
  constructor
  · intro hz
    rcases one_step_target_mem_exactChildren (tg := tg) hz with ⟨n, hzEq, hn⟩
    have hn' : n = dst := (hiff n).mp hn
    simpa [hn'] using hzEq
  · intro hz
    rcases hz with rfl
    exact hstep

theorem proxy_exact_nfXASqRightPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfXASqRightPred)) z
      ↔ z = exactNodeNF (.leaf .xa) := by
  exact proxy_exact_of_singleton
    (tg := .nfXASqRightPred)
    (dst := .leaf .xa)
    proxy_nfXASqRightPred_iff
    (by simpa [exactNodeNF, exactLeafNF] using nfXASqRightPred_steps_to_nfXA)

theorem proxy_exact_nfUSqLiftRightSPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfUSqLiftRightSPred)) z
      ↔ z = exactNodeNF (.leaf .u) := by
  exact proxy_exact_of_singleton
    (tg := .nfUSqLiftRightSPred)
    (dst := .leaf .u)
    proxy_nfUSqLiftRightSPred_iff
    (by simpa [exactNodeNF, exactLeafNF] using nfUSqLiftRightSPred_steps_to_nfU)

theorem proxy_exact_nfXADecorRightPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfXADecorRightPred)) z
      ↔ z = exactNodeNF (.leaf .xa) := by
  exact proxy_exact_of_singleton
    (tg := .nfXADecorRightPred)
    (dst := .leaf .xa)
    proxy_nfXADecorRightPred_iff
    (by
      have h :
          NFStepR (α := V) R4 nfXADecorRightPred nfXA :=
        decorRightKernel_exact_theorem.1
      simpa [exactNodeNF, exactLeafNF] using h)

theorem proxy_exact_nfUDecorLiftRightSPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfUDecorLiftRightSPred)) z
      ↔ z = exactNodeNF (.leaf .u) := by
  exact proxy_exact_of_singleton
    (tg := .nfUDecorLiftRightSPred)
    (dst := .leaf .u)
    proxy_nfUDecorLiftRightSPred_iff
    (by
      have h :
          NFStepR (α := V) R4 nfUDecorLiftRightSPred nfU :=
        decorRightKernel_exact_theorem.2.1
      simpa [exactNodeNF, exactLeafNF] using h)

theorem proxy_exact_nfXADecorLeftPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfXADecorLeftPred)) z
      ↔ z = exactNodeNF (.leaf .xa) := by
  exact proxy_exact_of_singleton
    (tg := .nfXADecorLeftPred)
    (dst := .leaf .xa)
    proxy_nfXADecorLeftPred_iff
    (by
      have h :
          NFStepR (α := V) R4 nfXADecorLeftPred nfXA :=
        decorLeftKernel_exact_theorem.1
      simpa [exactNodeNF, exactLeafNF] using h)

theorem proxy_exact_nfUDecorLiftLeftSPred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfUDecorLiftLeftSPred)) z
      ↔ z = exactNodeNF (.leaf .u) := by
  exact proxy_exact_of_singleton
    (tg := .nfUDecorLiftLeftSPred)
    (dst := .leaf .u)
    proxy_nfUDecorLiftLeftSPred_iff
    (by
      have h :
          NFStepR (α := V) R4 nfUDecorLiftLeftSPred nfU :=
        decorLeftKernel_exact_theorem.2.1
      simpa [exactNodeNF, exactLeafNF] using h)

theorem proxy_exact_nfUStablePred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfUStablePred)) z
      ↔ z = exactNodeNF (.leaf .u) := by
  exact proxy_exact_of_singleton
    (tg := .nfUStablePred)
    (dst := .leaf .u)
    proxy_nfUStablePred_iff
    (by
      have h :
          NFStepR (α := V) R4 nfUStablePred nfU :=
        stableKernel_codomain_theorem.1
      simpa [exactNodeNF, exactLeafNF] using h)

theorem proxy_exact_nfUHolePred
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.core .nfUHolePred)) z
      ↔ z = exactNodeNF (.leaf .u) := by
  exact proxy_exact_of_singleton
    (tg := .nfUHolePred)
    (dst := .leaf .u)
    proxy_nfUHolePred_iff
    nfUHolePred_steps_to_nfU

theorem core_target_one_step_exact
    (tg : CoreKernelTarget) {z : NormalForm V} :
    NFStepR (α := V) R4 (coreNFOfTarget tg) z
      ↔ ∃ dst : ExactNode,
          z = exactNodeNF dst
          ∧ OneStepProxyR4 (.core tg) dst := by
  constructor
  · intro hz
    rcases one_step_target_mem_exactChildren (tg := tg) hz with ⟨dst, hzEq, hmem⟩
    exact ⟨dst, hzEq, hmem⟩
  · rintro ⟨dst, rfl, hmem⟩
    cases tg with
    | nfXASqRightPred =>
        have hdst : dst = .leaf .xa := (proxy_nfXASqRightPred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfXASqRightPred (z := exactNodeNF (.leaf .xa))).2 rfl

    | nfUSqLiftRightSPred =>
        have hdst : dst = .leaf .u := (proxy_nfUSqLiftRightSPred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfUSqLiftRightSPred (z := exactNodeNF (.leaf .u))).2 rfl

    | nfXADecorRightPred =>
        have hdst : dst = .leaf .xa := (proxy_nfXADecorRightPred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfXADecorRightPred (z := exactNodeNF (.leaf .xa))).2 rfl

    | nfUDecorLiftRightSPred =>
        have hdst : dst = .leaf .u := (proxy_nfUDecorLiftRightSPred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfUDecorLiftRightSPred (z := exactNodeNF (.leaf .u))).2 rfl

    | nfXADecorLeftPred =>
        have hdst : dst = .leaf .xa := (proxy_nfXADecorLeftPred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfXADecorLeftPred (z := exactNodeNF (.leaf .xa))).2 rfl

    | nfUDecorLiftLeftSPred =>
        have hdst : dst = .leaf .u := (proxy_nfUDecorLiftLeftSPred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfUDecorLiftLeftSPred (z := exactNodeNF (.leaf .u))).2 rfl

    | nfUStablePred =>
        have hdst : dst = .leaf .u := (proxy_nfUStablePred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfUStablePred (z := exactNodeNF (.leaf .u))).2 rfl

    | nfUHolePred =>
        have hdst : dst = .leaf .u := (proxy_nfUHolePred_iff dst).mp hmem
        subst hdst
        exact (proxy_exact_nfUHolePred (z := exactNodeNF (.leaf .u))).2 rfl

    | nfUDecorHolePred =>
        rcases (proxy_nfUDecorHolePred_iff dst).mp hmem with hdst | hdst
        · subst hdst
          exact (proxy_exact_nfUDecorHolePred (z := exactNodeNF (.leaf .u))).2 (Or.inl rfl)
        · subst hdst
          exact (proxy_exact_nfUDecorHolePred (z := exactNodeNF (.core .nfUHolePred))).2 (Or.inr rfl)

    | nfXASqAPred =>
        rcases (proxy_nfXASqAPred_iff dst).mp hmem with hdst | hdst
        · subst hdst
          exact (proxy_exact_nfXASqAPred (z := exactNodeNF (.leaf .xa))).2 (Or.inl rfl)
        · subst hdst
          exact (proxy_exact_nfXASqAPred (z := exactNodeNF (.core .nfXASqRightPred))).2 (Or.inr rfl)

    | nfUSqLiftAPred =>
        rcases (proxy_nfUSqLiftAPred_iff dst).mp hmem with hdst | hdst
        · subst hdst
          exact (proxy_exact_nfUSqLiftAPred (z := exactNodeNF (.leaf .u))).2 (Or.inl rfl)
        · subst hdst
          exact (proxy_exact_nfUSqLiftAPred (z := exactNodeNF (.core .nfUSqLiftRightSPred))).2 (Or.inr rfl)

    | nfUDecorRightPred =>
        rcases (proxy_nfUDecorRightPred_iff dst).mp hmem with hdst | hdst
        · subst hdst
          exact (proxy_exact_nfUDecorRightPred (z := exactNodeNF (.leaf .u))).2 (Or.inl rfl)
        · subst hdst
          exact (proxy_exact_nfUDecorRightPred (z := exactNodeNF (.leaf .m))).2 (Or.inr rfl)

theorem core_target_proxy_child_realized
    (tg : CoreKernelTarget) (dst : ExactNode)
    (hmem : OneStepProxyR4 (.core tg) dst) :
    NFStepR (α := V) R4 (coreNFOfTarget tg) (exactNodeNF dst) := by
  exact (core_target_one_step_exact tg).2 ⟨dst, rfl, hmem⟩

private theorem leaf_xa_steps_to_leaf_v :
    NFStepR (α := V) R4 (exactNodeNF (.leaf .xa)) (exactNodeNF (.leaf .v)) := by
  simpa [exactNodeNF, exactLeafNF] using nfXA_steps_to_nfV

theorem no_step_from_leaf_u {z : NormalForm V} :
    ¬ NFStepR (α := V) R4 (exactNodeNF (.leaf .u)) z := by
  simpa [exactNodeNF, exactLeafNF] using no_NFStepR_from_nfU (z := z)

theorem no_step_from_leaf_m {z : NormalForm V} :
    ¬ NFStepR (α := V) R4 (exactNodeNF (.leaf .m)) z := by
  simpa [exactNodeNF, exactLeafNF] using no_NFStepR_from_nfM (z := z)

theorem no_step_from_leaf_v {z : NormalForm V} :
    ¬ NFStepR (α := V) R4 (exactNodeNF (.leaf .v)) z := by
  simpa [exactNodeNF, exactLeafNF] using no_NFStepR_from_nfV (z := z)

theorem leaf_exact_xa {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.leaf .xa)) z
      ↔ ∃ dst : ExactNode,
          z = exactNodeNF dst
          ∧ OneStepProxyR4 (.leaf .xa) dst := by
  constructor
  · intro hz
    have hzv : z = nfV := by
      exact NFStepR_from_nfXA_eq_nfV (z := z) (by simpa [exactNodeNF, exactLeafNF] using hz)
    refine ⟨.leaf .v, ?_, ?_⟩
    · simpa [exactNodeNF, exactLeafNF] using hzv
    · simp [OneStepProxyR4, exactOneStepChildrenR4]
  · rintro ⟨dst, rfl, hmem⟩
    have hdst : dst = .leaf .v := (proxy_leaf_xa_iff dst).mp hmem
    subst hdst
    exact leaf_xa_steps_to_leaf_v

theorem leaf_exact_u {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.leaf .u)) z
      ↔ ∃ dst : ExactNode,
          z = exactNodeNF dst
          ∧ OneStepProxyR4 (.leaf .u) dst := by
  constructor
  · intro hz
    exfalso
    exact no_step_from_leaf_u hz
  · rintro ⟨dst, _, hmem⟩
    simp [OneStepProxyR4, exactOneStepChildrenR4] at hmem

theorem leaf_exact_m {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.leaf .m)) z
      ↔ ∃ dst : ExactNode,
          z = exactNodeNF dst
          ∧ OneStepProxyR4 (.leaf .m) dst := by
  constructor
  · intro hz
    exfalso
    exact no_step_from_leaf_m hz
  · rintro ⟨dst, _, hmem⟩
    simp [OneStepProxyR4, exactOneStepChildrenR4] at hmem

theorem leaf_exact_v {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.leaf .v)) z
      ↔ ∃ dst : ExactNode,
          z = exactNodeNF dst
          ∧ OneStepProxyR4 (.leaf .v) dst := by
  constructor
  · intro hz
    exfalso
    exact no_step_from_leaf_v hz
  · rintro ⟨dst, _, hmem⟩
    simp [OneStepProxyR4, exactOneStepChildrenR4] at hmem

theorem exactNode_one_step_exact
    (src : ExactNode) {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF src) z
      ↔ ∃ dst : ExactNode,
          z = exactNodeNF dst
          ∧ OneStepProxyR4 src dst := by
  cases src with
  | core tg =>
      simpa [exactNodeNF] using core_target_one_step_exact (tg := tg) (z := z)
  | leaf ℓ =>
      cases ℓ with
      | xa =>
          simpa using leaf_exact_xa (z := z)
      | u =>
          simpa using leaf_exact_u (z := z)
      | m =>
          simpa using leaf_exact_m (z := z)
      | v =>
          simpa using leaf_exact_v (z := z)

theorem exactNode_proxy_child_realized
    (src dst : ExactNode)
    (hmem : OneStepProxyR4 src dst) :
    NFStepR (α := V) R4 (exactNodeNF src) (exactNodeNF dst) := by
  exact (exactNode_one_step_exact (src := src)).2 ⟨dst, rfl, hmem⟩

theorem exactNode_presents_R4_one_step
    (src : ExactNode) {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF src) z
      ↔ ∃ dst : ExactNode,
          z = exactNodeNF dst
          ∧ OneStepProxyR4 src dst := by
  exact exactNode_one_step_exact (src := src) (z := z)

theorem exactLeaf_xa_has_unique_successor
    {z : NormalForm V} :
    NFStepR (α := V) R4 (exactNodeNF (.leaf .xa)) z
      ↔ z = exactNodeNF (.leaf .v) := by
  constructor
  · intro hz
    rcases (exactNode_one_step_exact (src := .leaf .xa) (z := z)).1 hz with
      ⟨dst, hzEq, hmem⟩
    have hdst : dst = .leaf .v := by
      simpa [OneStepProxyR4, exactOneStepChildrenR4] using hmem
    simpa [hdst] using hzEq
  · intro hz
    subst hz
    exact exactNode_proxy_child_realized (.leaf .xa) (.leaf .v) (by
      simp [OneStepProxyR4, exactOneStepChildrenR4])

theorem exactTerminalLeaves_no_step :
    (∀ {z : NormalForm V},
        ¬ NFStepR (α := V) R4 (exactNodeNF (.leaf .u)) z) ∧
    (∀ {z : NormalForm V},
        ¬ NFStepR (α := V) R4 (exactNodeNF (.leaf .m)) z) ∧
    (∀ {z : NormalForm V},
        ¬ NFStepR (α := V) R4 (exactNodeNF (.leaf .v)) z) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rcases (exactNode_one_step_exact (src := .leaf .u) (z := z)).1 hz with
      ⟨dst, _, hmem⟩
    simp [OneStepProxyR4, exactOneStepChildrenR4] at hmem
  · intro z hz
    rcases (exactNode_one_step_exact (src := .leaf .m) (z := z)).1 hz with
      ⟨dst, _, hmem⟩
    simp [OneStepProxyR4, exactOneStepChildrenR4] at hmem
  · intro z hz
    rcases (exactNode_one_step_exact (src := .leaf .v) (z := z)).1 hz with
      ⟨dst, _, hmem⟩
    simp [OneStepProxyR4, exactOneStepChildrenR4] at hmem

end ExactNode
end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
