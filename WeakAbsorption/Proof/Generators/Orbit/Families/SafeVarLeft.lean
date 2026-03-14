import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Proof.Generators.Orbit.KDynamics

namespace WeakAbsorption
namespace WAA
namespace OrbitSafeVarLeft

open WeakAbsorption.Spec
open WeakAbsorption.WAA.OrbitKDynamics

section
variable {α : Type}

/-!
`x⋆□` を起点として、右穴に var を積む文脈
  D₀ = □
  D₁ = x⋆□
  D₂ = x⋆(x⋆□)
  D₃ = x⋆(x⋆(x⋆□))
  ...
を orbit の「安全な作用域」として定理化する。
-/

/-- Iterated right-var contexts: `iterRightVar a n` = `x⋆(x⋆(...⋆□))`. -/
def iterRightVar (a : α) : Nat → Ctx α
  | 0     => .hole
  | n + 1 => .right (Term.var a) (iterRightVar a n)

/-- Every `iterRightVar a n` is in `SafeCtxR`. -/
theorem safe_iterRightVar (a : α) : ∀ n, SafeCtxR (α := α) (iterRightVar (α := α) a n)
  | 0     => by
      simp [iterRightVar, SafeCtxR.hole]
  | n + 1 => by
      -- SafeCtxR.rightVar : SafeCtxR C → SafeCtxR (right (var a) C)
      exact SafeCtxR.rightVar (a := a) (safe_iterRightVar a n)

/--
Size offset of `iterRightVar a n` is exactly `2*n`.

Reason:
`Ctx.sizeOffset (right (var a) C) = sizeOffset C + size (var a) + 1 = sizeOffset C + 2`
since `size (var a) = 1`.
-/
theorem sizeOffset_iterRightVar (a : α) :
  ∀ n, Ctx.sizeOffset (α := α) (iterRightVar (α := α) a n) = 2 * n
  | 0 => by
      simp [iterRightVar, Ctx.sizeOffset]
  | n + 1 => by
    have ih := sizeOffset_iterRightVar a n
    simp [iterRightVar, Ctx.sizeOffset, ih, size, Nat.mul_succ, Nat.add_comm]
    rw [← Nat.add_assoc] -- 1 + (1 + 2 * n) を (1 + 1) + 2 * n に書き換え

/--
K-dynamics (budget theorem) specialized to the `x⋆(x⋆...□)` family:

If `size t ≤ K0` and `2*n ≤ Δ`, then `plug (iterRightVar a n) t` is visible at `K0+Δ`.
-/
theorem visible_iterRightVar_of_budget
  (K0 Δ : Nat) {t : Term α} (ht : size t ≤ K0) (a : α) (n : Nat) (hn : 2 * n ≤ Δ) :
  VisibleAt (α := α) (K0 + Δ) (iterRightVar (α := α) a n) t := by
  -- use the general budget lemma
  apply visibleAt_of_budget (α := α) K0 Δ (D := iterRightVar (α := α) a n) (t := t) ht
  -- show sizeOffset ≤ Δ
  have : Ctx.sizeOffset (α := α) (iterRightVar (α := α) a n) ≤ Δ := by
    simpa [sizeOffset_iterRightVar (α := α) a n] using hn
  exact this

/--
Orbit lifting for this family is unconditional (no `dom` burden),
because `SafeCtxR` gives total-domain normality preservation.
-/
theorem NFEqR_orbit_iterRightVar
  (a : α) (n : Nat) (R : RuleSet) {x y : NormalForm α} :
  NFEqR (α := α) R x y →
    NFEqR (α := α) R
      (plugNF (α := α) (iterRightVar (α := α) a n) x
        (SafeCtxR.dom (α := α) (safe_iterRightVar (α := α) a n) x))
      (plugNF (α := α) (iterRightVar (α := α) a n) y
        (SafeCtxR.dom (α := α) (safe_iterRightVar (α := α) a n) y)) := by
  intro hxy
  exact NFEqR_ctx_safeCtxR (α := α)
    (hD := safe_iterRightVar (α := α) a n)
    (R := R) hxy

end

end OrbitSafeVarLeft
end WAA
end WeakAbsorption
