import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure

import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Proof.Generators.Orbit.KDynamics
import WeakAbsorption.Proof.Generators.Orbit.Families.HoleLeftVar.Defs
import WeakAbsorption.Proof.Generators.Orbit.Invariants.LeafParityCtxFlipAll
import WeakAbsorption.Proof.Generators.Necessity.K11
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace WAA
namespace OrbitSafeMixedCtx

open WeakAbsorption.Spec
open WeakAbsorption.WAA.OrbitKDynamics
open WeakAbsorption.WAA.NecessityK11
open WeakAbsorption.WAA.OrbitLeafParityStabilityHoleLeftVar
open OrbitSafeHoleLeftVar
-- bring ctxFlipAll machinery (works for *all* contexts)


section
variable {α : Type}

/-! ############################################################
## Mixed context:  x ⋆ (□ ⋆ x)
############################################################ -/

/-- The mixed context `x⋆(□⋆x)` as a `Ctx`. -/
def mixCtx (a : α) : Ctx α :=
  -- right (var a) (left hole (var a))
  .right (Term.var a) (holeLeftVar (α := α) a)

/-- Unfolding of the plug: plug `mixCtx a` into `t` is `x ⋆ (t ⋆ x)`. -/
theorem plug_mixCtx (a : α) (t : Term α) :
  Ctx.plug (mixCtx (α := α) a) t = (Term.var a) ⋆ (t ⋆ (Term.var a)) := by
  simp [mixCtx, holeLeftVar, Ctx.plug]

/-! ------------------------------------------------------------
    Normality: partial action with the same DomNoC1 as □⋆x
------------------------------------------------------------ -/

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
      intro h
      rcases h with ⟨x, hx⟩
      cases hx

/--
If `t` is Normal and satisfies the same domain condition as `□⋆x`
(`DomNoC1 a t := ¬IsC1Root t (var a)`), then `mixCtx a` preserves normality:
`x⋆(t⋆x)` is Normal.
-/
theorem normal_plug_mixCtx
  (a : α) {t : Term α}
  (ht : Normal (α := α) t)
  (hDom : DomNoC1 (α := α) a t) :
  Normal (α := α) (Ctx.plug (mixCtx (α := α) a) t) := by
  -- First show rhs = (t⋆x) is normal via the □⋆x lemma
  have hInner : Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) t) :=
    normal_plug_holeLeftVar (α := α) a (t := t) ht hDom
  -- Now root is (var a ⋆ inner), always safe at root
  -- and plug_mixCtx rewrites to var a ⋆ (t⋆var a)
  -- Use Normal_op_iff.
  -- (var a ⋆ inner) with inner normal.
  have : Normal (α := α) ((Term.var a) ⋆ (Ctx.plug (holeLeftVar (α := α) a) t)) := by
    exact (Normal_op_iff (α := α) (Term.var a) (Ctx.plug (holeLeftVar (α := α) a) t)).2
      ⟨normal_var (α := α) a, hInner,
        not_IsC1Root_var_left (α := α) a (Ctx.plug (holeLeftVar (α := α) a) t),
        not_IsC2pRoot_var_left (α := α) a (Ctx.plug (holeLeftVar (α := α) a) t)⟩
  -- rewrite (var a ⋆ plug (□⋆a) t) into the stated shape
  simpa [mixCtx, holeLeftVar, Ctx.plug] using this

/-- dom for NormalForms under `mixCtx a` (same domain hypothesis as `□⋆a`). -/
theorem dom_mixCtx (a : α)
  (domNoC1 : ∀ z : NormalForm α, DomNoC1 (α := α) a z.1) :
  ∀ z : NormalForm α, Normal (α := α) (Ctx.plug (mixCtx (α := α) a) z.1) :=
by
  intro z
  exact normal_plug_mixCtx (α := α) a (t := z.1) z.2 (domNoC1 z)

/-- Orbit lifting for `mixCtx a` (partial action, via domNoC1). -/
theorem NFEqR_ctx_mixCtx
  (a : α) (R : RuleSet)
  (domNoC1 : ∀ z : NormalForm α, DomNoC1 (α := α) a z.1)
  {x y : NormalForm α} :
  NFEqR (α := α) R x y →
    NFEqR (α := α) R
      (plugNF (α := α) (mixCtx (α := α) a) x (dom_mixCtx (α := α) a domNoC1 x))
      (plugNF (α := α) (mixCtx (α := α) a) y (dom_mixCtx (α := α) a domNoC1 y)) :=
by
  intro hxy
  exact NFEqR_ctx (α := α)
    (D := mixCtx (α := α) a)
    (R := R)
    (dom := dom_mixCtx (α := α) a domNoC1)
    (x := x) (y := y) hxy

/-! ------------------------------------------------------------
    K-dynamics: sizeOffset for x⋆(□⋆x)
------------------------------------------------------------ -/

/-- `sizeOffset (□⋆a) = 2` already proved; here `sizeOffset (x⋆(□⋆x)) = 4`. -/
theorem sizeOffset_mixCtx (a : α) :
  Ctx.sizeOffset (α := α) (mixCtx (α := α) a) = 4 := by
  -- offset(right l C) = offset(C) + size l + 1, with l = var a, size = 1
  -- and offset(□⋆a)=2
  simp [mixCtx, Ctx.sizeOffset, size, sizeOffset_holeLeftVar (α := α) a]

/-- Pure size budget: `mixCtx` becomes visible by adding 4 to K. -/
theorem visible_mixCtx_of_size (a : α) (K0 : Nat) {t : Term α} (ht : size t ≤ K0) :
  VisibleAt (α := α) (K0 + 4) (mixCtx (α := α) a) t := by
  apply visibleAt_of_budget (α := α) K0 4 (D := mixCtx (α := α) a) (t := t) ht
  simp [sizeOffset_mixCtx (α := α) a]

/-! ------------------------------------------------------------
    Parity behavior via ctxFlipAll (this context does NOT flip parity)
------------------------------------------------------------ -/

/-- ctxFlipAll for `mixCtx` is `false`, so parity is preserved (not flipped). -/
theorem ctxFlipAll_mixCtx (a : α) :
  ctxFlipAll (α := α) (mixCtx (α := α) a) = false := by
  -- mixCtx = right (var a) (left hole (var a))
  -- ctxFlipAll = xor (leafParity var a) (xor (ctxFlipAll hole) (leafParity var a)) = true xor (false xor true) = false
  simp [mixCtx, ctxFlipAll, holeLeftVar, leafParity]

/-- Strong form: leafParity is preserved under `mixCtx`. -/
theorem leafParity_plug_mixCtx (a : α) (t : Term α) :
  leafParity (Ctx.plug (mixCtx (α := α) a) t) = leafParity t := by
  -- general formula: leafParity (plug C t) = xor (ctxFlipAll C) (leafParity t)
  have := leafParity_plug_ctxFlipAll (α := α) (mixCtx (α := α) a) t
  -- ctxFlipAll is false
  simpa [ctxFlipAll_mixCtx (α := α) a] using this

/--
Orbit stability (SqAbsorb-only) for `mixCtx`:

If leafParity differs at the core, it still differs after plugging by `mixCtx`,
so SqAbsorb-only cannot connect the orbit endpoints (when they are normal).
-/
theorem not_NFEqR_sqAbsorb_mixCtx_of_leafParity_ne
  (a : α) {x y : NormalForm α}
  (hx : Normal (α := α) (Ctx.plug (mixCtx (α := α) a) x.1))
  (hy : Normal (α := α) (Ctx.plug (mixCtx (α := α) a) y.1))
  (hne : leafParity x.1 ≠ leafParity y.1) :
  ¬ NFEqR (α := α) ([RuleId.SqAbsorb] : RuleSet)
      (plugNF (α := α) (mixCtx (α := α) a) x hx)
      (plugNF (α := α) (mixCtx (α := α) a) y hy) := by
  intro h
  have hpar :=
    NFEqR_sqAbsorb_preserves_leafParity (α := α)
      (x := plugNF (α := α) (mixCtx (α := α) a) x hx)
      (y := plugNF (α := α) (mixCtx (α := α) a) y hy)
      h
  have hplug : leafParity (Ctx.plug (mixCtx (α := α) a) x.1)
            = leafParity (Ctx.plug (mixCtx (α := α) a) y.1) := by
    simpa [plugNF] using hpar
  -- reflect back to the cores using Par.leafParity_eq_iff_plug
  have : leafParity x.1 = leafParity y.1 :=
    (leafParity_eq_iff_plug (α := α) (mixCtx (α := α) a) x.1 y.1).1 hplug
  exact hne this

end

end OrbitSafeMixedCtx
end WAA
end WeakAbsorption
