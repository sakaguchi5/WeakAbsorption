import WeakAbsorption.Proof.Generators.Vars1.Complete.Step4

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step5

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step0
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step3
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step4

/-!
Step5 (SAFE): Reduce the hard goal `GapTermAt → Vars1OrbitTpl` to a small “core template” obligation.

Key observation:
- For any fuel, `decomp fuel u v` gives a decomposition
    u = plug C u0, v = plug C v0
  (soundness of StripLite).
- Therefore, to prove `Vars1OrbitTpl u v`, it suffices to show
    Vars1CoreTpl u0 v0
  for some fuel (existential).
This removes the need to reason about the outer context directly.

So Step5 turns “gap ⇒ orbit” into:
  gap(u,v) ⇒ ∃fuel, Vars1CoreTpl (core(u,v,fuel))
which is exactly the shape that Step2 (orbit→core) and Step4/Step3 pipeline like.

Step6 will attack that remaining core-template obligation using the actual structure of NFRel/gap.
-/

section

-- ============================================================
-- 5.1  Orbit from “decomp core is a template”
-- ============================================================

/--
If for some fuel the stripped core (u0,v0) is a core template,
then the original pair is an orbit instance (witnessed by that decomposition).
-/
theorem orbit_of_decomp_coreTpl (fuel : Nat) (u v : Term V)
  (hTpl : let d := decomp (α := V) fuel u v; Vars1CoreTpl d.u0 d.v0) :
  Vars1OrbitTpl u v := by
  -- unpack the decomp record
  let d := decomp (α := V) fuel u v
  have hu : u = Ctx.plug d.C d.u0 := d.hu
  have hv : v = Ctx.plug d.C d.v0 := d.hv
  refine ⟨d.C, d.u0, d.v0, ?_, ?_, ?_⟩
  · exact (by simpa [d] using hTpl)
  · exact hu
  · exact hv

/--
Equivalently: to prove `GapTermAt R K u v → Vars1OrbitTpl u v`,
it suffices to prove `GapTermAt R K u v → ∃fuel, coreTpl(decomp fuel u v)`.
-/
theorem gapImpliesOrbit_of_existsFuel_coreTpl
  (R : RuleSet) (K : Nat)
  (hCore :
    ∀ u v : Term V, GapTermAt (R := R) K u v →
      ∃ fuel, (let d := decomp (α := V) fuel u v; Vars1CoreTpl d.u0 d.v0)) :
  ∀ u v : Term V, GapTermAt (R := R) K u v → Vars1OrbitTpl u v := by
  intro u v hGap
  rcases hCore u v hGap with ⟨fuel, hTpl⟩
  exact orbit_of_decomp_coreTpl (fuel := fuel) (u := u) (v := v) hTpl

-- ============================================================
-- 5.2  A canonical fuel choice (K-general friendly)
-- ============================================================

/--
A canonical “big enough” fuel:
`fuel := size u + size v`.

This avoids ∃fuel noise later: it pins the stripping procedure to a deterministic budget.
(It does NOT claim maximality—only gives you a stable target to prove templates about.)
-/
def coreFuel (u v : Term V) : Nat := size u + size v

/-- Core extracted using the canonical fuel. -/
def coreU (u v : Term V) : Term V :=
  (decomp (α := V) (coreFuel u v) u v).u0

def coreV (u v : Term V) : Term V :=
  (decomp (α := V) (coreFuel u v) u v).v0

/--
If you can prove template membership for the canonical coreFuel, then you get orbit.
-/
theorem orbit_of_coreFuel_coreTpl (u v : Term V)
  (hTpl : Vars1CoreTpl (coreU u v) (coreV u v)) :
  Vars1OrbitTpl u v := by
  -- rewrite to the previous lemma form
  have : (let d := decomp (α := V) (coreFuel u v) u v; Vars1CoreTpl d.u0 d.v0) := by
    -- by definition coreU/coreV are those projections
    simpa [coreU, coreV, coreFuel]
  exact orbit_of_decomp_coreTpl (fuel := coreFuel u v) (u := u) (v := v) this

-- ============================================================
-- 5.3  Step5 obligations for R=[] and R=[SqAbsorb]
-- ============================================================

/--
Step5 obligation form (canonical fuel):
For a given (R,K), every raw gap instance has its canonical stripped core in Vars1CoreTpl.
-/
def GapCoreTplAt (R : RuleSet) (K : Nat) : Prop :=
  ∀ u v : Term V, GapTermAt (R := R) K u v → Vars1CoreTpl (coreU u v) (coreV u v)

/--
If `GapCoreTplAt R K` holds, then raw gaps imply orbit (and Step4 pipeline closes).
-/
theorem gapImpliesOrbit_of_GapCoreTplAt (R : RuleSet) (K : Nat)
  (h : GapCoreTplAt (R := R) K) :
  ∀ u v : Term V, GapTermAt (R := R) K u v → Vars1OrbitTpl u v := by
  intro u v hGap
  -- canonical fuel gives orbit directly
  exact orbit_of_coreFuel_coreTpl (u := u) (v := v) (hTpl := h u v hGap)

/-
So the *real remaining work* is now isolated:

(★) prove `GapCoreTplAt R K` for `R=[]` and `R=[SqAbsorb]`, for all K≥11.

Once (★) is done, Step4’s theorem
  coveredByExists_rawGap_of_gapImpliesOrbit
plus Step2’s core recovery closes vars=1 gap-classification by core templates.
-/

end

end Step5
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
