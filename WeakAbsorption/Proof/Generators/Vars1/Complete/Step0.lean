import WeakAbsorption.Proof.Generators.Orbit.KDynamics
import WeakAbsorption.Proof.Generators.Utils.StripLite
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step0

open WeakAbsorption
open WeakAbsorption.WAA.OrbitKDynamics
open WeakAbsorption.Proof.Generators.StripLite

section
variable {α : Type} [DecidableEq α]

/-!
Step0 (K-general, vars-agnostic):

We DO NOT classify NormalForms here.
We only package:

- Visibility under a K bound is governed by `sizeOffset`.
- Any two terms can be decomposed as `u = plug C u0`, `v = plug C v0` via `StripLite.stripMany`,
  without maximality/uniqueness.
- This gives a “core+context” language in Proof.

This file is the stable bridge between Tooling observations and Proof-side theorems.
-/

-- ------------------------------------------------------------
-- 0.1 Visibility: K increase reveals more contexts (already proved in OrbitKDynamics)
-- ------------------------------------------------------------
omit [DecidableEq α] in
/-- Re-export: `VisibleAt K D t ↔ size t + sizeOffset D ≤ K`. -/
theorem visibleAt_iff' (K : Nat) (D : Ctx α) (t : Term α) :
  VisibleAt (α := α) K D t ↔ size t + WeakAbsorption.WAA.Ctx.sizeOffset (α := α) D ≤ K := by
  simpa using (visibleAt_iff (α := α) (K := K) (D := D) (t := t))
omit [DecidableEq α] in
/-- Re-export: budget lemma `size t ≤ K0` and `sizeOffset D ≤ Δ` ⇒ visible at `K0+Δ`. -/
theorem visibleAt_of_budget' (K0 Δ : Nat) {D : Ctx α} {t : Term α}
  (ht : size t ≤ K0) (hD : WeakAbsorption.WAA.Ctx.sizeOffset (α := α) D ≤ Δ) :
  VisibleAt (α := α) (K0 + Δ) D t := by
  simpa using (visibleAt_of_budget (α := α) K0 Δ (D := D) (t := t) ht hD)

-- ------------------------------------------------------------
-- 0.2 Core+context decomposition via StripLite (no maximality)
-- ------------------------------------------------------------

/--
A K-neutral decomposition record:
`u = plug C u0` and `v = plug C v0`.
-/
structure Decomp (u v : Term α) where
  C  : Ctx α
  u0 : Term α
  v0 : Term α
  hu : u = Ctx.plug C u0
  hv : v = Ctx.plug C v0

/-- Produce a decomposition using `stripMany` (fuel-bounded). -/
def decomp (fuel : Nat) (u v : Term α) : Decomp (α := α) u v :=
  let r := stripMany (α := α) fuel u v
  have hs := stripMany_sound (α := α) fuel u v
  { C  := r.1
    u0 := r.2.1
    v0 := r.2.2
    hu := hs.1
    hv := hs.2 }

/--
Soundness: `decomp` is always correct (trivial, but useful for rewriting).
-/
theorem decomp_sound (fuel : Nat) (u v : Term α) :
  let d := decomp (α := α) fuel u v
  (u = Ctx.plug d.C d.u0) ∧ (v = Ctx.plug d.C d.v0) := by
  intro d
  exact ⟨d.hu, d.hv⟩

-- ------------------------------------------------------------
-- 0.3 What Step1 will need (spelled out as hypotheses)
-- ------------------------------------------------------------

/-!
Step1 will specialize to vars=1 and aims to prove that for certain relations (e.g. NFRel / RedEq)
the resulting `(u0,v0)` must fall into a finite set of core templates.

To avoid accidental overreach, we record the exact kind of hypothesis needed:
"core templates cover all decomposed pairs that satisfy a target predicate P".
-/

/-- A “core template set” represented as a predicate on pairs of terms. -/
abbrev CoreTpl (α : Type) := Term α → Term α → Prop

/--
Coverage statement template:

Given a predicate `P u v` (e.g. `NFRel` between NormalForms, or Tooling's “gap” property),
and a template predicate `T` describing the finite set of cores,

we will aim to prove:
  P u v → T u0 v0
for `(u0,v0)` obtained by `decomp`.
-/
def CoveredBy (P : Term α → Term α → Prop) (T : CoreTpl α) : Prop :=
  ∀ (fuel : Nat) (u v : Term α),
    P u v →
    let d := decomp (α := α) fuel u v
    T d.u0 d.v0

end

end Step0
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
