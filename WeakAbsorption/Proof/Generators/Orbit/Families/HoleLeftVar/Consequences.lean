import WeakAbsorption.Proof.Generators.Orbit.Families.HoleLeftVar.Witnesses
import WeakAbsorption.Proof.Generators.Orbit.KDynamics
import WeakAbsorption.Proof.Generators.Necessity.K11
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace WAA
namespace OrbitSafeHoleLeftVar
namespace Consequences

open WeakAbsorption.Spec
open WeakAbsorption.WAA.OrbitKDynamics
open WeakAbsorption.WAA.NecessityK11

section
variable {α : Type} (a : α)

open WeakAbsorption.WAA.OrbitSafeHoleLeftVar.Witnesses

/-
Goal of this file:
Turn the witness computations about ctx = (□⋆x) into proof-side consequences:

1) The observable ctx=(□⋆x) patterns come from the fact that
   holeLeftVar a maps the *core* endpoints
     X ↦ S,  A ↦ Au
   and both images are normal and within the K=11 window (sizeOffset=2).

2) Under SqAbsorb-only, the orbit-visible pair (Au, S) is *still* not connectable by NFEqR,
   witnessed by the leafParity invariant (no new generator requirement is created by orbit exposure).
-/

/- ------------------------------------------------------------
   1) Exact images under ctx = (□⋆a)
------------------------------------------------------------ -/

theorem plug_holeLeftVar_X :
  Ctx.plug (holeLeftVar (α := α) a) (X (a := a)) = S (a := a) := by
  simp [holeLeftVar, S, X, Ctx.plug]

theorem plug_holeLeftVar_A :
  Ctx.plug (holeLeftVar (α := α) a) (A (a := a)) = Au (a := a) := by
  simp [holeLeftVar, Au, A, S, X, Ctx.plug]

/- ------------------------------------------------------------
   2) K-dynamics: why K=11 is exactly where this ctx becomes “visible”
------------------------------------------------------------ -/

private theorem size_X : size (X (a := a)) = 1 := by
  simp [X, size]

private theorem size_A : size (A (a := a)) = 7 := by
  simp [A, S, X, size]

/-- In K-dynamics terms, `□⋆a` has offset 2. -/
theorem sizeOffset_holeLeftVar' :
  Ctx.sizeOffset (α := α) (holeLeftVar (α := α) a) = 2 := by
  simpa using sizeOffset_holeLeftVar (α := α) a

/-- `X` is visible under `□⋆a` already at K=3 (and hence at K=11). -/
theorem visible_K11_holeLeftVar_X :
  VisibleAt (α := α) 11 (holeLeftVar (α := α) a) (X (a := a)) := by
  -- size X + offset 2 ≤ 11
  have : size (X (a := a)) + Ctx.sizeOffset (α := α) (holeLeftVar (α := α) a) ≤ 11 := by
    simp [size_X (a := a), sizeOffset_holeLeftVar' (a := a)]
  exact (visibleAt_iff (α := α) (K := 11) (D := holeLeftVar (α := α) a) (t := X (a := a))).2 this

/-- `A` is visible under `□⋆a` at K=11 because 7 + 2 ≤ 11. -/
theorem visible_K11_holeLeftVar_A :
  VisibleAt (α := α) 11 (holeLeftVar (α := α) a) (A (a := a)) := by
  have : size (A (a := a)) + Ctx.sizeOffset (α := α) (holeLeftVar (α := α) a) ≤ 11 := by
    simp [size_A (a := a), sizeOffset_holeLeftVar' (a := a)]
  exact (visibleAt_iff (α := α) (K := 11) (D := holeLeftVar (α := α) a) (t := A (a := a))).2 this

/- ------------------------------------------------------------
   3) Normality domain facts (why this is a partial action)
------------------------------------------------------------ -/

theorem DomNoC1_X : DomNoC1 (α := α) a (X (a := a)) := by
  intro h
  rcases h with ⟨w, hw⟩
  cases hw

theorem DomNoC1_A :
  DomNoC1 (α := α) a (A (a := a)) :=
  WeakAbsorption.WAA.OrbitSafeHoleLeftVar.Witnesses.DomNoC1_A (a := a)

theorem not_DomNoC1_S :
  ¬ DomNoC1 (α := α) a (S (a := a)) :=
  WeakAbsorption.WAA.OrbitSafeHoleLeftVar.Witnesses.not_DomNoC1_S (a := a)

theorem not_DomNoC1_Au :
  ¬ DomNoC1 (α := α) a (Au (a := a)) :=
  WeakAbsorption.WAA.OrbitSafeHoleLeftVar.Witnesses.not_DomNoC1_Au (a := a)

/-- The good case: plugging `A` into `□⋆a` stays normal (and equals `Au`). -/
theorem normal_plug_holeLeftVar_A :
  Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) (A (a := a))) :=
  plug_holeLeftVar_A_normal (a := a)

/-- The bad case: plugging `S` into `□⋆a` is not normal (C1 fires). -/
theorem not_normal_plug_holeLeftVar_S :
  ¬ Normal (α := α) (Ctx.plug (holeLeftVar (α := α) a) (S (a := a))) :=
  WeakAbsorption.WAA.OrbitSafeHoleLeftVar.Witnesses.not_normal_plug_holeLeftVar_S (a := a)

/- ------------------------------------------------------------
   4) Orbit does not create a *new* generator requirement:
      SqAbsorb-only still cannot connect the orbit-visible pair (Au, S).
------------------------------------------------------------ -/

/-- NormalForm wrappers for S and Au (needed to talk about `NFEqR`). -/
def nfS : NormalForm α := ⟨S (a := a), S_normal (a := a)⟩
def nfAu : NormalForm α := ⟨Au (a := a), Au_normal (a := a)⟩

private theorem leafParity_S :
  leafParity (S (a := a)) = false := by
  simp [leafParity, S, X]

private theorem leafParity_Au :
  leafParity (Au (a := a)) = true := by
  simp [leafParity, Au, A, S, X]

/--
Key consequence (K=11 story, generator side):

Even though `Au` and `S` are both normal and become visible under ctx=(□⋆x),
they are **not** connectable by `NFEqR [SqAbsorb]`.

So exposing orbit-variants by increasing K does not, by itself, demand new generators;
the obstruction is already present at the core level (parity invariant).
-/
theorem not_NFEqR_sqAbsorb_Au_S :
  ¬ NFEqR (α := α) ([RuleId.SqAbsorb] : RuleSet) (nfAu (a := a)) (nfS (a := a)) := by
  intro h
  have hpar :=
    NFEqR_sqAbsorb_preserves_leafParity (α := α)
      (x := nfAu (a := a)) (y := nfS (a := a)) h
  have : leafParity (Au (a := a)) = leafParity (S (a := a)) := by
    simpa [nfAu, nfS] using hpar
  -- Au parity = true, S parity = false
  simpa [leafParity_Au (a := a), leafParity_S (a := a),this]

/-
Optional “executive summary” lemma:
The observable ctx=(□⋆x) core-pattern at K=11 corresponds exactly to the image of (A, X)
under `holeLeftVar`, and the SqAbsorb-only generator system still cannot connect that image.
-/
theorem orbit_explains_ctxHoleLeftVar_K11 :
  VisibleAt (α := α) 11 (holeLeftVar (α := α) a) (X (a := a))
  ∧ VisibleAt (α := α) 11 (holeLeftVar (α := α) a) (A (a := a))
  ∧ Ctx.plug (holeLeftVar (α := α) a) (X (a := a)) = S (a := a)
  ∧ Ctx.plug (holeLeftVar (α := α) a) (A (a := a)) = Au (a := a)
  ∧ ¬ NFEqR (α := α) ([RuleId.SqAbsorb] : RuleSet) (nfAu (a := a)) (nfS (a := a)) :=
by
  refine ⟨visible_K11_holeLeftVar_X (a := a),
          visible_K11_holeLeftVar_A (a := a),
          plug_holeLeftVar_X (a := a),
          plug_holeLeftVar_A (a := a),
          not_NFEqR_sqAbsorb_Au_S (a := a)⟩

end

end Consequences
end OrbitSafeHoleLeftVar
end WAA
end WeakAbsorption
