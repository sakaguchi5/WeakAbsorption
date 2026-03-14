import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Measure
import WeakAbsorption.Core.Rewrite

import WeakAbsorption.Proof.Generators.Orbit.KDynamics
import WeakAbsorption.Proof.Generators.Orbit.Families.MixedCtx.Defs
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace WAA
namespace OrbitSafeMixedCtxK11K13Witness

open WeakAbsorption.Spec
open WeakAbsorption.WAA.OrbitKDynamics
open WeakAbsorption.WAA.OrbitSafeMixedCtx

section
variable {α : Type} (a : α)

-- Concrete vars=1-style terms
def X : Term α := Term.var a
def S : Term α := (X (a := a)) ⋆ (X (a := a))
def A : Term α := (S (a := a)) ⋆ (S (a := a))
def Au : Term α := (A (a := a)) ⋆ (X (a := a))

-- Size computations (purely structural)
theorem size_X : size (X (a := a)) = 1 := by
  simp [X, size]

theorem size_S : size (S (a := a)) = 3 := by
  simp [S, X, size]

theorem size_A : size (A (a := a)) = 7 := by
  simp [A, S, X, size]

theorem size_Au : size (Au (a := a)) = 9 := by
  simp [Au, A, S, X, size]

/--
Key “visibility gap” (pure K-dynamics):

`mixCtx` has offset 4, so plugging a size-9 term is:
- NOT visible at K=11 (since 9+4=13>11),
- visible at K=13 (since 9+4=13≤13).

This matches the observed phenomenon:
`ctx = x⋆(□⋆x)` starts showing up only when K reaches 13.
-/
theorem not_visible_K11_but_visible_K13_for_Au :
  ¬ VisibleAt (α := α) 11 (mixCtx (α := α) a) (Au (a := a))
  ∧ VisibleAt (α := α) 13 (mixCtx (α := α) a) (Au (a := a)) :=
by
  constructor
  · -- not visible at 11
    -- Use visibleAt_iff: VisibleAt K D t ↔ size t + offset ≤ K
    intro h
    have hineq :
      size (Au (a := a)) + Ctx.sizeOffset (α := α) (mixCtx (α := α) a) ≤ 11 :=
      (visibleAt_iff (α := α) (K := 11) (D := mixCtx (α := α) a) (t := Au (a := a))).1 h
    -- But size(Au)=9 and offset(mixCtx)=4 => LHS=13
    have : 13 ≤ 11 := by
      simp [size_Au (a := a), sizeOffset_mixCtx (α := α) a] at hineq
    exact (by decide : ¬ 13 ≤ 11) this
  · -- visible at 13
    -- budget lemma with K0=9, Δ=4
    have ht : size (Au (a := a)) ≤ 9 := by
      simp [size_Au (a := a)]
    have hvis : VisibleAt (α := α) (9 + 4) (mixCtx (α := α) a) (Au (a := a)) :=
      visible_mixCtx_of_size (α := α) (a := a) 9 (t := Au (a := a)) ht
    -- 9+4 = 13
    simpa using hvis

end

end OrbitSafeMixedCtxK11K13Witness
end WAA
end WeakAbsorption
