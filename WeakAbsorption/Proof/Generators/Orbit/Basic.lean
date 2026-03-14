import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Equational
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure

import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace WAA

open WeakAbsorption.Spec
open WeakAbsorption.Closure
/-!
Orbit lemmas (Proof-side)

We formalize a partial “action” of contexts on NormalForm, and prove:

1) Context composition on `Ctx` and its plug law.
2) Each generator step (SqAbsorb/SqStable/C2C1/Decor/DoubleSq) lifts under an outer context.
3) Therefore, `NFStepR` lifts under an outer context.
4) Therefore, `NFEqR` lifts under an outer context **if** the context preserves normality
   for every intermediate NormalForm (we encode this as a domain hypothesis).
-/

section
variable {α : Type}

/- ------------------------------------------------------------
   Context composition (outer ∘ inner)
   ------------------------------------------------------------ -/

/-- Compose contexts: `comp D C` means “first plug into C, then into D”. -/
def Ctx.comp : Ctx α → Ctx α → Ctx α
  | .hole,        C => C
  | .left D r,    C => .left (Ctx.comp D C) r
  | .right l D,   C => .right l (Ctx.comp D C)

/-- Plug law for context composition. -/
theorem Ctx.plug_comp (D C : Ctx α) (t : Term α) :
  Ctx.plug D (Ctx.plug C t) = Ctx.plug (Ctx.comp D C) t := by
  induction D with
  | hole =>
      simp [Ctx.comp, Ctx.plug]
  | left D r ih =>
      simp [Ctx.comp, Ctx.plug, ih]
  | right l D ih =>
      simp [Ctx.comp, Ctx.plug, ih]
/- ------------------------------------------------------------
   Size under contexts (orbit-friendly arithmetic)
   ------------------------------------------------------------ -/

/-- Size offset contributed by a context (independent of the plugged term). -/
def Ctx.sizeOffset {α : Type} : Ctx α → Nat
  | .hole        => 0
  | .left C r    => Ctx.sizeOffset C + size r + 1
  | .right l C   => Ctx.sizeOffset C + size l + 1

/-- Exact size law: plugging adds a fixed offset determined by the context. -/
theorem size_plug {α : Type} (C : Ctx α) (t : Term α) :
  size (Ctx.plug C t) = size t + Ctx.sizeOffset (α := α) C := by
  induction C with
  | hole =>
      simp [Ctx.plug, Ctx.sizeOffset]
  | left C r ih =>
      -- plug (left C r) t = (plug C t) ⋆ r
      simp [Ctx.plug, Ctx.sizeOffset, size, ih, Nat.add_left_comm, Nat.add_comm]
  | right l C ih =>
      -- plug (right l C) t = l ⋆ (plug C t)
      simp [Ctx.plug, Ctx.sizeOffset, size, ih,  Nat.add_left_comm, Nat.add_comm]

/-- Monotone bound: plugging preserves ≤ with an additive offset. -/
theorem size_plug_le {α : Type} (C : Ctx α) {t : Term α} {K : Nat} :
  size t ≤ K → size (Ctx.plug C t) ≤ K + Ctx.sizeOffset (α := α) C := by
  intro ht
  -- size (plug C t) = size t + off
  have := Nat.add_le_add_right ht (Ctx.sizeOffset (α := α) C)
  simpa [size_plug (α := α) C t] using this

/-- Offset of composed contexts is additive. -/
theorem Ctx.sizeOffset_comp {α : Type} (D C : Ctx α) :
  Ctx.sizeOffset (α := α) (Ctx.comp D C)
    = Ctx.sizeOffset (α := α) D + Ctx.sizeOffset (α := α) C := by
  induction D with
  | hole =>
      simp [Ctx.comp, Ctx.sizeOffset]
  | left D r ih =>
      simp [Ctx.comp, Ctx.sizeOffset, ih,  Nat.add_left_comm, Nat.add_comm]
  | right l D ih =>
      simp [Ctx.comp, Ctx.sizeOffset, ih,  Nat.add_left_comm, Nat.add_comm]

/-- Size along a two-stage plug (outer ∘ inner) expands additively. -/
theorem size_plug_plug {α : Type} (D C : Ctx α) (t : Term α) :
  size (Ctx.plug D (Ctx.plug C t))
    = size t + Ctx.sizeOffset (α := α) C + Ctx.sizeOffset (α := α) D := by
  -- Use plug_comp + additivity of offsets
  calc
    size (Ctx.plug D (Ctx.plug C t))
        = size (Ctx.plug (Ctx.comp D C) t) := by
            simp [Ctx.plug_comp]
    _   = size t + Ctx.sizeOffset (α := α) (Ctx.comp D C) := by
            simp [size_plug]
    _   = size t + (Ctx.sizeOffset (α := α) D + Ctx.sizeOffset (α := α) C) := by
            simp [Ctx.sizeOffset_comp]
    _   = size t + Ctx.sizeOffset (α := α) C + Ctx.sizeOffset (α := α) D := by
            simp [ Nat.add_left_comm, Nat.add_comm]
/- ------------------------------------------------------------
   Context action on NormalForm (partial: needs a Normal proof)
   ------------------------------------------------------------ -/

/-- Plug a NormalForm under an outer context, requiring a Normal proof. -/
def plugNF (D : Ctx α) (x : NormalForm α) (hx : Normal (Ctx.plug D x.1)) : NormalForm α :=
  ⟨Ctx.plug D x.1, hx⟩

/-- NFRel is closed under outer contexts (given normality of the results). -/
theorem NFRel_ctx (D : Ctx α) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  NFRel (α := α) x y → NFRel (α := α) (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  intro h
  -- NFRel = RedEq on underlying terms
  dsimp [NFRel, plugNF] at *
  exact RedEq_ctx (α := α) D h

/- ------------------------------------------------------------
   Step lifting (this is the core orbit lemma)
   ------------------------------------------------------------ -/

private theorem NFSqStepCtx_ctx (D : Ctx α) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  NFSqStepCtx (α := α) x y →
    NFSqStepCtx (α := α) (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  rintro ⟨C, t, u, hx0, hy0⟩
  refine ⟨Ctx.comp D C, t, u, ?_, ?_⟩
  · dsimp [plugNF]
    rw [hx0]
    simp [Ctx.plug_comp]
  · dsimp [plugNF]
    rw [hy0]
    simp [Ctx.plug_comp]

private theorem NFSqStableStepCtx_ctx (D : Ctx α) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  NFSqStableStepCtx (α := α) x y →
    NFSqStableStepCtx (α := α) (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  rintro ⟨C, t, u, hx0, hy0⟩
  refine ⟨Ctx.comp D C, t, u, ?_, ?_⟩
  · dsimp [plugNF]; rw [hx0]; simp [Ctx.plug_comp]
  · dsimp [plugNF]; rw [hy0]; simp [Ctx.plug_comp]

private theorem NFC2C1StepCtx_ctx (D : Ctx α) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  NFC2C1StepCtx (α := α) x y →
    NFC2C1StepCtx (α := α) (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  rintro ⟨C, x0, p, z, hx0, hy0⟩
  refine ⟨Ctx.comp D C, x0, p, z, ?_, ?_⟩
  · dsimp [plugNF]; rw [hx0]; simp [Ctx.plug_comp]
  · dsimp [plugNF]; rw [hy0]; simp [Ctx.plug_comp]

private theorem NFDecorStepCtx_ctx (D : Ctx α) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  NFDecorStepCtx (α := α) x y →
    NFDecorStepCtx (α := α) (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  rintro ⟨C, t, u, hx0, hy0⟩
  refine ⟨Ctx.comp D C, t, u, ?_, ?_⟩
  · dsimp [plugNF]; rw [hx0]; simp [Ctx.plug_comp]
  · dsimp [plugNF]; rw [hy0]; simp [Ctx.plug_comp]

private theorem NFDoubleSqStepCtx_ctx (D : Ctx α) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  NFDoubleSqStepCtx (α := α) x y →
    NFDoubleSqStepCtx (α := α) (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  rintro ⟨C, t, u, hx0, hy0⟩
  refine ⟨Ctx.comp D C, t, u, ?_, ?_⟩
  · dsimp [plugNF]; rw [hx0]; simp [Ctx.plug_comp]
  · dsimp [plugNF]; rw [hy0]; simp [Ctx.plug_comp]

/-- General step-lifting for the Kernel `step` dispatch. -/
theorem step_ctx (D : Ctx α) (tag : RuleId) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  step (α := α) tag x y →
    step (α := α) tag (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  cases tag <;> intro h
  · -- SqAbsorb
    exact NFSqStepCtx_ctx (α := α) D (x := x) (y := y) hx hy h
  · -- SqStable
    exact NFSqStableStepCtx_ctx (α := α) D (x := x) (y := y) hx hy h
  · -- C2C1
    exact NFC2C1StepCtx_ctx (α := α) D (x := x) (y := y) hx hy h
  · -- Decor
    exact NFDecorStepCtx_ctx (α := α) D (x := x) (y := y) hx hy h
  · -- DoubleSq
    exact NFDoubleSqStepCtx_ctx (α := α) D (x := x) (y := y) hx hy h

/-- Lift one step under an outer context (domain is just the endpoints). -/
theorem NFStepR_ctx (D : Ctx α) (R : RuleSet) {x y : NormalForm α}
  (hx : Normal (Ctx.plug D x.1)) (hy : Normal (Ctx.plug D y.1)) :
  NFStepR (α := α) R x y →
    NFStepR (α := α) R (plugNF (α := α) D x hx) (plugNF (α := α) D y hy) := by
  rintro ⟨tag, hmem, hstep⟩
  refine ⟨tag, hmem, ?_⟩
  exact step_ctx (α := α) D tag (x := x) (y := y) hx hy hstep

/--
Lifting an entire `NFEqR` derivation requires that the context keeps *every*
intermediate NormalForm normal after plugging. We encode that as a “domain”
hypothesis `dom : ∀ z, Normal (plug D z.1)`.
-/
theorem NFEqR_ctx (D : Ctx α) (R : RuleSet)
  (dom : ∀ z : NormalForm α, Normal (Ctx.plug D z.1)) {x y : NormalForm α} :
  NFEqR (α := α) R x y →
    NFEqR (α := α) R
      (plugNF (α := α) D x (dom x))
      (plugNF (α := α) D y (dom y)) := by
  intro h
  induction h with
  | rel a b hab =>
      -- 1ステップの持ち上げを利用
      apply EqvGen.rel
      exact NFStepR_ctx (α := α) D R (dom a) (dom b) hab
  | refl a =>
      -- エラー箇所: 明示的に plugNF 後の値に対する refl であることを指定
      exact EqvGen.refl (plugNF (α := α) D a (dom a))
  | symm a b _ ih =>
      -- 推論を助けるため、中間状態を _ で渡す
      exact EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 =>
      -- 推論を助けるため、中間状態を _ で渡す
      exact EqvGen.trans _ _ _ ih1 ih2

/- ------------------------------------------------------------
   B) Sufficient conditions for `dom` (total-domain contexts)
   ------------------------------------------------------------ -/

/--
`SafeCtxR` = contexts of the form `x ⋆ (x ⋆ ... (x ⋆ □) ...)` (hole on the right),
i.e. iterated `Ctx.right (var a) _`.

For such contexts, plugging preserves normality for *every* normal term,
hence yields a genuine `dom : ∀ z : NormalForm α, Normal (plug D z.1)`.
-/
inductive SafeCtxR : Ctx α → Prop where
  | hole : SafeCtxR (.hole)
  | rightVar (a : α) {C : Ctx α} : SafeCtxR C → SafeCtxR (.right (Term.var a) C)

private theorem normal_var (a : α) : Normal (α := α) (Term.var a) := by
  intro u hu
  cases hu with
  | step _ _ hs => cases hs

private theorem not_IsC1Root_var_left (a : α) (u : Term α) :
  ¬ IsC1Root (α := α) (Term.var a) u := by
  rintro ⟨x, hx⟩
  cases hx

private theorem not_IsC2pRoot_var_left (a : α) (u : Term α) :
  ¬ IsC2pRoot (α := α) (Term.var a) u := by
  cases u with
  | var b =>
      simp [IsC2pRoot]
  | op y z =>
      -- IsC2pRoot (var a) (y⋆z) means ∃x, var a = (x⋆y)⋆z, impossible
      intro h
      rcases h with ⟨x, hx⟩
      cases hx

/-- SafeCtxR preserves normality when plugging a normal term. -/
theorem SafeCtxR.normal_plug {D : Ctx α} (hD : SafeCtxR (α := α) D) {t : Term α} :
  Normal (α := α) t → Normal (α := α) (Ctx.plug D t) := by
  intro ht
  induction hD with
  | hole =>
      -- Ctx.plug .hole t = t なので、仮定 ht から自明。
      exact ht
  | rightVar a hC ih =>
      -- 1. 目標を Ctx.plug の定義に従って展開する。
      --    これを行うことで、Lean は D が (.right (Term.var a) C✝) であることを認識します。
      rw [Ctx.plug]

      -- 2. Normal_op_iff を適用して、演算 (var a ⋆ plug C✝ t) の正規性を確認。
      apply (Normal_op_iff (α := α) (Term.var a) (Ctx.plug _ t)).mpr

      -- 3. 各条件を埋める
      refine ⟨normal_var (α := α) a, ih, ?_, ?_⟩
      · -- C1 ルール (var a ⋆ ...) は簡約不可
        exact not_IsC1Root_var_left (α := α) a (Ctx.plug _ t)
      · -- C2p ルール (var a ⋆ ...) は簡約不可
        exact not_IsC2pRoot_var_left (α := α) a (Ctx.plug _ t)

/-- From `SafeCtxR D`, we get a total-domain `dom` for `NFEqR_ctx`. -/
theorem SafeCtxR.dom {D : Ctx α} (hD : SafeCtxR (α := α) D) :
  ∀ z : NormalForm α, Normal (α := α) (Ctx.plug D z.1) :=
by
  intro z
  exact SafeCtxR.normal_plug (α := α) hD (t := z.1) z.2

/-- Orbit lifting becomes *unconditional* for `SafeCtxR` contexts. -/
theorem NFEqR_ctx_safeCtxR {D : Ctx α} (hD : SafeCtxR (α := α) D) (R : RuleSet) {x y : NormalForm α} :
  NFEqR (α := α) R x y →
    NFEqR (α := α) R
      (plugNF (α := α) D x (SafeCtxR.dom (α := α) hD x))
      (plugNF (α := α) D y (SafeCtxR.dom (α := α) hD y)) :=
by
  exact NFEqR_ctx (α := α) (D := D) (R := R) (dom := SafeCtxR.dom (α := α) hD)


end

end WAA
end WeakAbsorption
