import WeakAbsorption.Proof.Generators.Vars1.Complete.Step5
import WeakAbsorption.Core.Measure

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step6

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

open WeakAbsorption.Proof.Generators.StripLite
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step0
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step5

/-!
Step6: Canonical-fuel core templates from orbit instances.

We prove a key strengthening:

  Vars1OrbitTpl u v → Vars1CoreTpl (coreU u v) (coreV u v)

i.e. once you know a pair is an orbit of a core template, the *canonical* stripping fuel
`coreFuel := size u + size v` is guaranteed to be enough to recover the core template.

Consequently, if you can show `GapTermAt R K u v → Vars1OrbitTpl u v`,
then you immediately get `GapCoreTplAt R K`.
-/

section

-- ============================================================
-- 6.1  Size facts (very small)
-- ============================================================

/-- Every term has size ≥ 1. -/
theorem one_le_size (t : Term V) : 1 ≤ size t := by
  cases t with
  | var a =>
      simp [size]
  | op t u =>
      -- size (op t u) is a successor, hence ≥ 1
      simp [size]

/-- Steps are bounded by the size of a plugged term. -/
theorem steps_le_size_plug (C : Ctx V) (t : Term V) :
  Ctx.steps C ≤ size (Ctx.plug C t) := by
  induction C with
  | hole =>
      simp [Ctx.steps, Ctx.plug]
  | left C r ih =>
      -- plug (left C r) t = (plug C t) ⋆ r
      -- size increases by at least 1
      -- steps: steps C + 1
      -- size: size (plug C t) + size r + 1
      have h1 : Ctx.steps C + 1 ≤ size (Ctx.plug C t) + 1 := by
        exact Nat.add_le_add_right ih 1
      have h2 : size (Ctx.plug C t) + 1 ≤ size (Ctx.plug C t) + size r + 1 := by
        -- since 1 ≤ size r + 1 (trivial), add size(plug C t) on left
        -- a + 1 ≤ a + (size r) + 1
        exact Nat.add_le_add_left (Nat.le_add_left 1 (size r)) (size (Ctx.plug C t))
      -- finish
      simpa [Ctx.steps, Ctx.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.le_trans h1 h2
  | right l C ih =>
      -- h1: steps C + 1 ≤ size (plug C t) + 1
      have h1 : Ctx.steps C + 1 ≤ size (Ctx.plug C t) + 1 :=
        Nat.add_le_add_right ih 1
      have h2 : size (Ctx.plug C t) + 1 ≤ size l + size (Ctx.plug C t) + 1 :=
        -- 両辺に +1 があるので、それを除いた size (plug C t) ≤ size l + size (plug C t) を証明すればよい
        Nat.add_le_add_right (Nat.le_add_left (size (Ctx.plug C t)) (size l)) 1
      simpa [Ctx.steps, Ctx.plug, size, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.le_trans h1 h2

-- ============================================================
-- 6.2  Strengthen core recovery: any fuel ≥ steps(C)+1 works
-- ============================================================

/--
If a pair is an orbit instance of a core template (u0,v0) under context C,
then stripping with ANY fuel ≥ steps(C)+1 recovers exactly (C,u0,v0).
-/
theorem stripMany_plug_coreTpl_of_ge
  (C : Ctx V) {u0 v0 : Term V} (hTpl : Vars1CoreTpl u0 v0)
  (fuel : Nat) (hFuel : Ctx.steps C + 1 ≤ fuel) :
  stripMany (α := V) fuel (Ctx.plug C u0) (Ctx.plug C v0) = (C, u0, v0) := by
  induction C generalizing fuel with
  | hole =>
      -- fuel cannot be 0
      cases fuel with
      | zero =>
          cases hFuel
      | succ fuel =>
          have hOnce : stripOnce (α := V) u0 v0 = (Ctx.hole, u0, v0) :=
            stripOnce_coreTpl (h := hTpl)
          -- stripMany (succ _) stops immediately because fst(stripOnce)=hole
          simp [stripMany, Ctx.plug, hOnce]
  | left C r ih =>
      cases fuel with
      | zero =>
          cases hFuel
      | succ fuel =>
          -- derive the reduced fuel bound for the inner context
          have hFuel' : Ctx.steps C + 1 ≤ fuel := by
            -- hFuel : (steps (left C r) + 1) ≤ succ fuel
            -- steps(left C r)+1 = succ(steps C + 1)
            have : Nat.succ (Ctx.steps C + 1) ≤ Nat.succ fuel := by
              simpa [Ctx.steps, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hFuel
            exact Nat.le_of_succ_le_succ this
          -- peel one left layer (right child matches r)
          -- then recurse
          have ih' := ih (fuel := fuel) hFuel'
          -- simp performs the peel and comp reconstruction
          simp [stripMany, stripOnce, Ctx.plug, ih', Ctx.comp_left_hole,]
  | right l C ih =>
      cases fuel with
      | zero =>
          cases hFuel
      | succ fuel =>
          have hFuel' : Ctx.steps C + 1 ≤ fuel := by
            have : Nat.succ (Ctx.steps C + 1) ≤ Nat.succ fuel := by
              simpa [Ctx.steps, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hFuel
            exact Nat.le_of_succ_le_succ this
          -- right-child equality would imply u0=v0; exclude using core_ne_of_tpl + injectivity
          have hNe : ¬ (Ctx.plug C u0 = Ctx.plug C v0) := by
            exact plug_ne_of_core_ne (C := C) (u0 := u0) (v0 := v0) (core_ne_of_tpl hTpl)
          have ih' := ih (fuel := fuel) hFuel'
          simp [stripMany, stripOnce, Ctx.plug, ih', hNe, Ctx.comp_right_hole,]

-- ============================================================
-- 6.3  Orbit ⇒ canonical coreFuel template membership
-- ============================================================

/--
Orbit instance implies canonical-fuel core template:

If `Vars1OrbitTpl u v`, then `(coreU u v, coreV u v)` is in `Vars1CoreTpl`.
-/
theorem coreTpl_of_orbit (u v : Term V) :
  Vars1OrbitTpl u v → Vars1CoreTpl (coreU u v) (coreV u v) := by
  intro h
  rcases h with ⟨C, u0, v0, hTpl, hu, hv⟩
  subst hu; subst hv
  -- Canonical fuel for this particular orbit pair
  -- fuel := size (plug C u0) + size (plug C v0)
  have hStep : Ctx.steps C ≤ size (Ctx.plug C u0) :=
    steps_le_size_plug (C := C) (t := u0)
  have hPos  : 1 ≤ size (Ctx.plug C v0) :=
    one_le_size (Ctx.plug C v0)
  have hFuel : Ctx.steps C + 1 ≤ coreFuel (Ctx.plug C u0) (Ctx.plug C v0) := by
    -- coreFuel = size u + size v
    simpa [coreFuel] using Nat.add_le_add hStep hPos

  -- Core recovery at any fuel ≥ steps(C)+1
  have hStrip :
      stripMany (α := V)
        (coreFuel (Ctx.plug C u0) (Ctx.plug C v0))
        (Ctx.plug C u0) (Ctx.plug C v0)
      = (C, u0, v0) :=
    stripMany_plug_coreTpl_of_ge
      (C := C) (u0 := u0) (v0 := v0) (hTpl := hTpl)
      (fuel := coreFuel (Ctx.plug C u0) (Ctx.plug C v0)) hFuel
  --projection を “明示的に” 引き出す
  have hU :
      (stripMany (α := V)
        (coreFuel (Ctx.plug C u0) (Ctx.plug C v0))
        (Ctx.plug C u0) (Ctx.plug C v0)).2.1 = u0 := by
    -- stripMany ... = (C,u0,v0) から .2.1 = u0
    simp [hStrip]
  have hV :
      (stripMany (α := V)
        (coreFuel (Ctx.plug C u0) (Ctx.plug C v0))
        (Ctx.plug C u0) (Ctx.plug C v0)).2.2 = v0 := by
    simp [hStrip]
  -- coreU/coreV を “projection” にまで展開して書き換える
  have hCoreU :
      coreU (Ctx.plug C u0) (Ctx.plug C v0) = u0 := by
    -- coreU u v = (decomp (coreFuel u v) u v).u0
    --          = (stripMany (coreFuel u v) u v).2.1
    -- なので hU で落ちる
    -- （Step0.decomp は record だが .u0 は r.2.1 なので simp が効く）
    simpa [coreU, Step0.decomp, coreFuel] using hU
  have hCoreV :
      coreV (Ctx.plug C u0) (Ctx.plug C v0) = v0 := by
    simpa [coreV, Step0.decomp, coreFuel] using hV
  -- 最後に hTpl を transport
  -- いま欲しいのは Vars1CoreTpl (coreU u v) (coreV u v)
  -- だが coreU/coreV が u0/v0 に等しいので置換できる
  simpa [hCoreU, hCoreV] using hTpl

-- ============================================================
-- 6.4  Final Step6 bridge: gapImpliesOrbit ⇒ GapCoreTplAt
-- ============================================================

/--
If raw gaps imply orbit (Step5’s remaining bridge),
then raw gaps also satisfy the canonical-fuel core template obligation `GapCoreTplAt`.
-/
theorem GapCoreTplAt_of_gapImpliesOrbit
  (R : RuleSet) (K : Nat)
  (gapImpliesOrbit : ∀ u v : Term V, GapTermAt (R := R) K u v → Vars1OrbitTpl u v) :
  GapCoreTplAt (R := R) K := by
  intro u v hGap
  have horb : Vars1OrbitTpl u v := gapImpliesOrbit u v hGap
  exact coreTpl_of_orbit (u := u) (v := v) horb

end

end Step6
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
