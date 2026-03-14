import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Spec.Rule
import WeakAbsorption.Core.Measure

namespace WeakAbsorption
namespace WAA
namespace OrbitKDynamics

open WeakAbsorption.Spec

section
variable {α : Type}

/-! ############################################################
## 1) 「文脈が見える条件」を sizeOffset で完全定式化
############################################################ -/

/-- “Visible at K” means the plugged term fits under the size bound K. -/
def VisibleAt (K : Nat) (D : Ctx α) (t : Term α) : Prop :=
  size (Ctx.plug D t) ≤ K

/-- Exact visibility equation via `sizeOffset`. -/
theorem visibleAt_iff (K : Nat) (D : Ctx α) (t : Term α) :
  VisibleAt (α := α) K D t ↔ size t + Ctx.sizeOffset (α := α) D ≤ K := by
  simp [VisibleAt, size_plug (α := α) D t]

/-- If a context is visible at K, then its offset is ≤ K. -/
theorem sizeOffset_le_of_visible {K : Nat} {D : Ctx α} {t : Term α} :
  VisibleAt (α := α) K D t → Ctx.sizeOffset (α := α) D ≤ K := by
  intro h
  -- sizeOffset D ≤ size t + sizeOffset D = size (plug D t) ≤ K
  have h1 : Ctx.sizeOffset (α := α) D ≤ size t + Ctx.sizeOffset (α := α) D :=
    Nat.le_add_left _ _
  have h2 : Ctx.sizeOffset (α := α) D ≤ size (Ctx.plug D t) := by
    simp [size_plug (α := α) D t,h1]
  exact Nat.le_trans h2 h

/-- If a context is visible at K, then the underlying term is also ≤ K. -/
theorem size_le_of_visible {K : Nat} {D : Ctx α} {t : Term α} :
  VisibleAt (α := α) K D t → size t ≤ K := by
  intro h
  -- size t ≤ size t + offset = size (plug D t) ≤ K
  have h1 : size t ≤ size t + Ctx.sizeOffset (α := α) D :=
    Nat.le_add_right _ _
  have h2 : size t ≤ size (Ctx.plug D t) := by
    simp [size_plug (α := α) D t,h1]
  exact Nat.le_trans h2 h

/-- Monotonicity in K. -/
theorem visibleAt_mono {K₁ K₂ : Nat} (hK : K₁ ≤ K₂) {D : Ctx α} {t : Term α} :
  VisibleAt (α := α) K₁ D t → VisibleAt (α := α) K₂ D t :=
by intro h; exact Nat.le_trans h hK

/-! ############################################################
## 2) K増加で出現する orbit を上界付きで証明
############################################################ -/

/--
Budget lemma (upper bound):
If `size t ≤ K0` and `sizeOffset D ≤ Δ`, then `plug D t` is visible at `K0 + Δ`.
This is the core “K increases reveal more contexts” theorem.
-/
theorem visibleAt_of_budget (K0 Δ : Nat) {D : Ctx α} {t : Term α}
  (ht : size t ≤ K0) (hD : Ctx.sizeOffset (α := α) D ≤ Δ) :
  VisibleAt (α := α) (K0 + Δ) D t := by
  -- size (plug D t) = size t + offset ≤ K0 + Δ
  have : size t + Ctx.sizeOffset (α := α) D ≤ K0 + Δ :=
    Nat.add_le_add ht hD
  simpa [visibleAt_iff (α := α) (K := K0 + Δ) (D := D) (t := t)] using this

/--
Window theorem:
Fix a base bound `K0` and a term `t` with `size t ≤ K0`.
Then *all* contexts with `sizeOffset ≤ Δ` become visible once you raise K by Δ.
-/
theorem visibleAt_window (K0 Δ : Nat) {t : Term α} (ht : size t ≤ K0) :
  ∀ D : Ctx α, Ctx.sizeOffset (α := α) D ≤ Δ → VisibleAt (α := α) (K0 + Δ) D t :=
by
  intro D hD
  exact visibleAt_of_budget (α := α) K0 Δ ht hD

/-- Additivity reminder: offsets add under context composition. -/
theorem sizeOffset_additive (D C : Ctx α) :
  Ctx.sizeOffset (α := α) (Ctx.comp D C)
    = Ctx.sizeOffset (α := α) D + Ctx.sizeOffset (α := α) C :=
by simpa using (Ctx.sizeOffset_comp (α := α) D C)

/-! ############################################################
## 3) 「生成器必然性の順番」を理論化（orbitは新しい生成器要件を生まない）
############################################################ -/

/--
Main principle (one-step → orbit):
If `x ~_R y` (i.e. `NFEqR R x y`) is already provable at the core level,
then for any `SafeCtxR` outer context `D`, the same generator set `R` also proves
the orbit instance `D·x ~_R D·y` (no new generators needed for the orbit).

This is the precise proof-side form of:
“K increases only reveals context variants; it does not create new generator requirements.”
-/
theorem NFEqR_orbit_safeCtxR
  {D : Ctx α} (hD : SafeCtxR (α := α) D) (R : RuleSet) {x y : NormalForm α} :
  NFEqR (α := α) R x y →
    NFEqR (α := α) R
      (plugNF (α := α) D x (SafeCtxR.dom (α := α) hD x))
      (plugNF (α := α) D y (SafeCtxR.dom (α := α) hD y)) :=
by
  exact NFEqR_ctx_safeCtxR (α := α) (hD := hD) (R := R)

/--
Bounded orbit lifting:
If core endpoints fit in `K0` and `sizeOffset D ≤ Δ`, then the orbit endpoints fit in `K0+Δ`,
and the same generator proof lifts under `SafeCtxR`.
-/
theorem NFEqR_orbit_safeCtxR_bounded
  (K0 Δ : Nat) {D : Ctx α} (hD : SafeCtxR (α := α) D)
  (hOff : Ctx.sizeOffset (α := α) D ≤ Δ)
  {x y : NormalForm α} (hx : size x.1 ≤ K0) (hy : size y.1 ≤ K0)
  (R : RuleSet) (hxy : NFEqR (α := α) R x y) :
  (size (Ctx.plug D x.1) ≤ K0 + Δ)
  ∧ (size (Ctx.plug D y.1) ≤ K0 + Δ)
  ∧ NFEqR (α := α) R
      (plugNF (α := α) D x (SafeCtxR.dom (α := α) hD x))
      (plugNF (α := α) D y (SafeCtxR.dom (α := α) hD y)) :=
by
  refine ⟨?_, ?_, ?_⟩
  · -- size bound for x
    exact visibleAt_of_budget (α := α) K0 Δ (D := D) (t := x.1) hx hOff
  · -- size bound for y
    exact visibleAt_of_budget (α := α) K0 Δ (D := D) (t := y.1) hy hOff
  · -- orbit lifting of the generator proof
    exact NFEqR_orbit_safeCtxR (α := α) (hD := hD) (R := R) hxy

end

end OrbitKDynamics
end WAA
end WeakAbsorption
