import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Proof.Generators.Orbit.KDynamics
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure

namespace WeakAbsorption
namespace WAA
namespace OrbitSafeHoleLeftVar

open WeakAbsorption.Spec
open WeakAbsorption.WAA.OrbitKDynamics

section
variable {α : Type}

/-!
(2)  □⋆x  (= left-hole with right var) is NOT total-domain safe.

We formalize it as a **partial action**:
for a fixed variable `a : α`, define the context

  D₁(a) := (□ ⋆ var a) = Ctx.left Ctx.hole (var a)

Then:
- Plugging preserves normality if the plugged normal term is **not** a C1-root against `var a`.
- Under that domain hypothesis (domNoC1), orbit lifting of `NFEqR` works.

We also connect it to K-dynamics via `sizeOffset = 2`.
-/

/-- The basic left-hole context: `□ ⋆ var a`. -/
def holeLeftVar (a : α) : Ctx α :=
  .left .hole (Term.var a)

/-- Domain predicate: a normal term is “safe” if it is NOT a C1-root against `var a`. -/
def DomNoC1 (a : α) (t : Term α) : Prop :=
  ¬ IsC1Root (α := α) t (Term.var a)

/-- For right operand a var, C2p-root can never fire. -/
theorem not_IsC2pRoot_rightVar (a : α) (t : Term α) :
  ¬ IsC2pRoot (α := α) t (Term.var a) := by
  -- IsC2pRoot t u requires u = (y⋆z). For u=var a it's false by definition.
  simp [IsC2pRoot]

/--
Key normality lemma for (2):

If `t` is Normal and not a C1-root against `var a`,
then `t ⋆ var a` is Normal.
-/
theorem normal_plug_holeLeftVar
  (a : α) {t : Term α}
  (ht : Normal (α := α) t)
  (hC1 : DomNoC1 (α := α) a t) :
  Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) t) := by
  -- plug (□⋆a) t = t ⋆ var a
  simp [holeLeftVar, Ctx.plug]
  -- Normal_op_iff gives the four conjuncts
  apply (Normal_op_iff (α := α) t (Term.var a)).2
  refine ⟨ht, ?_, ?_, ?_⟩
  · -- var is Normal
    intro u hu
    cases hu with
    | step _ _ hs => cases hs
  · -- not C1-root: exactly hC1
    simpa [DomNoC1] using hC1
  · -- not C2p-root: always for right var
    exact not_IsC2pRoot_rightVar (α := α) a t

/-- Turn the domain predicate into a “dom” for NormalForms under `□⋆a`. -/
theorem dom_holeLeftVar (a : α)
  (domNoC1 : ∀ z : NormalForm α, DomNoC1 (α := α) a z.1) :
  ∀ z : NormalForm α, Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) z.1) :=
by
  intro z
  exact normal_plug_holeLeftVar (α := α) a (t := z.1) z.2 (domNoC1 z)

/--
Orbit lifting for `□⋆a` (partial action):

If `domNoC1` holds for every intermediate NormalForm (encoded as a ∀-hypothesis),
then `NFEqR` proofs lift under `□⋆a`.
-/
theorem NFEqR_ctx_holeLeftVar
  (a : α) (R : RuleSet)
  (domNoC1 : ∀ z : NormalForm α, DomNoC1 (α := α) a z.1)
  {x y : NormalForm α} :
  NFEqR (α := α) R x y →
    NFEqR (α := α) R
      (plugNF (α := α) (holeLeftVar (α := α) a) x (dom_holeLeftVar (α := α) a domNoC1 x))
      (plugNF (α := α) (holeLeftVar (α := α) a) y (dom_holeLeftVar (α := α) a domNoC1 y)) :=
by
  -- We can reuse the generic lifting theorem from Orbit.lean
  intro hxy
  exact NFEqR_ctx (α := α)
    (D := holeLeftVar (α := α) a)
    (R := R)
    (dom := dom_holeLeftVar (α := α) a domNoC1)
    (x := x) (y := y) hxy

/-! ------------------------------------------------------------
    K-dynamics specialization for □⋆a
------------------------------------------------------------ -/

/-- `sizeOffset (□⋆a) = 2`. -/
theorem sizeOffset_holeLeftVar (a : α) :
  Ctx.sizeOffset (α := α) (holeLeftVar (α := α) a) = 2 := by
  simp [holeLeftVar, Ctx.sizeOffset, size]

/--
Budget form: if `size t ≤ K0`, then `(t⋆a)` is visible at `K0+2`.
(This is purely size; normality needs `DomNoC1` separately.)
-/
theorem visible_holeLeftVar_of_size (a : α) (K0 : Nat) {t : Term α} (ht : size t ≤ K0) :
  VisibleAt (α := α) (K0 + 2) (holeLeftVar (α := α) a) t := by
  -- use visibleAt_of_budget with Δ=2
  apply visibleAt_of_budget (α := α) K0 2 (D := holeLeftVar (α := α) a) (t := t) ht
  simp [sizeOffset_holeLeftVar (α := α) a]

end

end OrbitSafeHoleLeftVar
end WAA
end WeakAbsorption
