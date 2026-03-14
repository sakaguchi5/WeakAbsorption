import WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
import WeakAbsorption.Proof.Generators.Orbit.KDynamics
import WeakAbsorption.Proof.Generators.Utils.StripLite
import WeakAbsorption.Core.Measure
import WeakAbsorption.Core.Rewrite

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step2

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.WAA.OrbitKDynamics
open WeakAbsorption.Proof.Generators.StripLite
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1

/-!
Step2 (SAFE): Orbit-closure coverage without classifying all NormalForms.

What we do here:
- We do NOT attempt “vars=1 NormalForm classification”.
- We prove a robust, structural statement:

    If (u,v) is obtained by plugging the same context C into a core-template pair (u0,v0),
    then stripMany (with enough fuel) recovers exactly (C,u0,v0).

- Using this, orbit coverage becomes a one-liner:
    Vars1OrbitTpl u v → ∃ fuel, decomp fuel u v has a core in Vars1CoreTpl.

- Finally, we keep the K-general side packaged:
    visibility is governed by sizeOffset (already in KDynamics),
    and we provide concrete budgets for the two vars=1 cores.
-/

section

-- We work in vars=1
open WeakAbsorption.SmallCheck

-- ============================================================
-- 2.1  Basic utilities: injectivity of plug, step-count, comp lemmas
-- ============================================================

/-- `Ctx.plug` is structurally injective in the plugged term. -/
theorem Ctx.plug_injective {α : Type} :
  ∀ (C : Ctx α) {t u : Term α}, Ctx.plug C t = Ctx.plug C u → t = u := by
  intro C
  induction C with
  | hole =>
      intro t u h
      simpa [Ctx.plug] using h
  | left C r ih =>
      intro t u h
      have : Ctx.plug C t = Ctx.plug C u := by
        injection h with hL hR
      exact ih this
  | right l C ih =>
      intro t u h
      have : Ctx.plug C t = Ctx.plug C u := by
        injection h with hL hR
      exact ih this

/-- A fuel upper bound: number of outer context layers. -/
def Ctx.steps {α : Type} : Ctx α → Nat
  | .hole        => 0
  | .left C _    => Ctx.steps C + 1
  | .right _ C   => Ctx.steps C + 1

/-- Composition helpers when the peeled layer is `left hole r`. -/
theorem Ctx.comp_left_hole {α : Type} (r : Term α) (C : Ctx α) :
  Ctx.comp (α := α) (Ctx.left Ctx.hole r) C = Ctx.left C r := by
  simp [Ctx.comp]

/-- Composition helpers when the peeled layer is `right l hole`. -/
theorem Ctx.comp_right_hole {α : Type} (l : Term α) (C : Ctx α) :
  Ctx.comp (α := α) (Ctx.right l Ctx.hole) C = Ctx.right l C := by
  simp [Ctx.comp]

-- ============================================================
-- 2.2  Core-template plumbing: keep orbit-coverage proofs tiny
-- ============================================================

-- Small symmetry helpers (used to avoid re-proving trivial inequalities)
theorem s_ne_A : s ≠ A := by
  intro h
  exact A_ne_s (by simpa using h.symm)

theorem Au_ne_A : Au ≠ A := by
  intro h
  have hs : size Au = size A := congrArg size h
  simp [size_Au, size_A] at hs

theorem A_ne_Au : A ≠ Au := by
  intro h
  exact Au_ne_A (by simpa using h.symm)

/-- `(s,A)` stops immediately: `stripOnce s A = (hole,s,A)`. -/
theorem stripOnce_s_A :
  stripOnce (α := V) s A = (Ctx.hole, s, A) := by
  have hR : x ≠ s := x_ne_s
  have hL : x ≠ s := x_ne_s
  simp [stripOnce, s, A, x]

/-- `(A,Au)` stops immediately: `stripOnce A Au = (hole,A,Au)`. -/
theorem stripOnce_A_Au :
  stripOnce (α := V) A Au = (Ctx.hole, A, Au) := by
  have hR : s ≠ x := s_ne_x
  have hL : s ≠ A := s_ne_A
  simp [stripOnce, A, Au, s, x]

/-- Any vars=1 core template pair is a “stop core”: `stripOnce u0 v0 = (hole,u0,v0)`. -/
theorem stripOnce_coreTpl {u0 v0 : Term V} (h : Vars1CoreTpl u0 v0) :
  stripOnce (α := V) u0 v0 = (Ctx.hole, u0, v0) := by
  rcases h with h | h | h | h
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact stripOnce_A_s
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact stripOnce_s_A
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact stripOnce_Au_A
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact stripOnce_A_Au

/-- Any vars=1 core template pair has distinct endpoints (used to kill right-branch `if`). -/
theorem core_ne_of_tpl {u0 v0 : Term V} (h : Vars1CoreTpl u0 v0) : u0 ≠ v0 := by
  rcases h with h | h | h | h
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact A_ne_s
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact s_ne_A
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact Au_ne_A
  · rcases h with ⟨hu, hv⟩; subst hu; subst hv; exact A_ne_Au

/-- If cores differ, their images under the same context differ (by injectivity). -/
theorem plug_ne_of_core_ne (C : Ctx V) {u0 v0 : Term V} (hne : u0 ≠ v0) :
  Ctx.plug C u0 ≠ Ctx.plug C v0 := by
  intro hEq
  have : u0 = v0 := Ctx.plug_injective (α := V) C hEq
  exact hne this

-- ============================================================
-- 2.3  Core recovery lemma (SAFE heart of Step2)
-- ============================================================

/--
General “core recovery”:

If (u,v) = (plug C u0, plug C v0) and (u0,v0) is a core template,
then stripping with fuel = steps(C)+1 recovers exactly (C,u0,v0).
-/
theorem stripMany_plug_coreTpl (C : Ctx V) {u0 v0 : Term V} (hTpl : Vars1CoreTpl u0 v0) :
  stripMany (α := V) (Ctx.steps C + 1) (Ctx.plug C u0) (Ctx.plug C v0) = (C, u0, v0) := by
  induction C with
  | hole =>
      have hOnce : stripOnce (α := V) u0 v0 = (Ctx.hole, u0, v0) :=
        stripOnce_coreTpl (h := hTpl)
      -- With C=hole, stripMany 1 stops immediately.
      simp [Ctx.plug, stripMany, hOnce]
  | left C r ih =>
      -- Right child matches, so stripOnce peels a left-hole layer.
      simp [Ctx.steps, stripMany, stripOnce, Ctx.plug, ih, Ctx.comp_left_hole]
  | right l C ih =>
      -- Right-child equality would imply u0=v0 (by injectivity), contradicting core_ne_of_tpl.
      have hNe : ¬ (Ctx.plug C u0 = Ctx.plug C v0) := by
        exact plug_ne_of_core_ne (C := C) (u0 := u0) (v0 := v0) (core_ne_of_tpl hTpl)
      simp [Ctx.steps, stripMany, stripOnce, Ctx.plug, ih, hNe, Ctx.comp_right_hole]

-- ============================================================
-- 2.4  Orbit predicate + ∃fuel coverage (now tiny)
-- ============================================================

/--
Orbit closure (lite):

(u,v) is an orbit-variant iff there exist a context C and a core-template pair (u0,v0)
such that u = plug C u0 and v = plug C v0.
-/
def Vars1OrbitTpl (u v : Term V) : Prop :=
  ∃ C u0 v0, Vars1CoreTpl u0 v0 ∧ u = Ctx.plug C u0 ∧ v = Ctx.plug C v0

/--
SAFE coverage theorem (existential fuel):

If (u,v) is an orbit-variant of a core template, then there exists a fuel such that
`Step0.decomp fuel u v` lands in the core template predicate.

This avoids any full NormalForm classification and avoids “∀fuel” overreach.
-/
theorem coveredBy_templates_on_orbits_existsFuel (u v : Term V) :
  Vars1OrbitTpl u v →
  ∃ fuel,
    let d := Step0.decomp (α := V) fuel u v
    Vars1CoreTpl d.u0 d.v0 := by
  intro h
  rcases h with ⟨C, u0, v0, hTpl, hu, hv⟩
  refine ⟨Ctx.steps C + 1, ?_⟩
  subst hu; subst hv
  -- decomp fuel (plug C u0) (plug C v0) uses stripMany fuel as its core extractor,
  -- and stripMany_plug_coreTpl recovers exactly (C,u0,v0).
  simp [Step0.decomp, stripMany_plug_coreTpl (C := C) (hTpl := hTpl), hTpl]

-- ============================================================
-- 2.5  K-general packaging: size bounds for vars=1 cores + context offsets
-- ============================================================

/--
Size of a plugged term is `size t + sizeOffset C` (re-export of `size_plug`).
-/
theorem size_plug_bound (C : Ctx V) (t : Term V) :
  size (Ctx.plug C t) = size t + WeakAbsorption.WAA.Ctx.sizeOffset (α := V) C := by
  simpa using (WeakAbsorption.WAA.size_plug (α := V) C t)

/-- Concrete K-budgets for the SqAbsorb core (A,s). -/
theorem visible_orbit_A_s (_K0 Δ : Nat) (C : Ctx V)
  (hC : WeakAbsorption.WAA.Ctx.sizeOffset (α := V) C ≤ Δ) :
  VisibleAt (α := V) (7 + Δ) C A ∧ VisibleAt (α := V) (3 + Δ) C s := by
  have hA : size A ≤ 7 := by simp [size_A]
  have hs : size s ≤ 3 := by simp [size_s]
  refine ⟨?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (visibleAt_of_budget (α := V) 7 Δ (D := C) (t := A) hA hC)
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (visibleAt_of_budget (α := V) 3 Δ (D := C) (t := s) hs hC)

/-- Concrete K-budgets for the SqStable core (Au,A). -/
theorem visible_orbit_Au_A (_K0 Δ : Nat) (C : Ctx V)
  (hC : WeakAbsorption.WAA.Ctx.sizeOffset (α := V) C ≤ Δ) :
  VisibleAt (α := V) (9 + Δ) C Au ∧ VisibleAt (α := V) (7 + Δ) C A := by
  have hAu : size Au ≤ 9 := by simp [size_Au]
  have hA : size A ≤ 7 := by simp [size_A]
  refine ⟨?_, ?_⟩
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (visibleAt_of_budget (α := V) 9 Δ (D := C) (t := Au) hAu hC)
  · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (visibleAt_of_budget (α := V) 7 Δ (D := C) (t := A) hA hC)

end

end Step2
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
