import WeakAbsorption.Proof.Generators.Vars1.Complete.Step14
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step13
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step10
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step7
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step2

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step15

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck
open WeakAbsorption.WAA

open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step2
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step7
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step10
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step13
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step14

/-!
Step15: (two halves)
  - Part A (後者): supply the two gap obligations (R=[] / R=[SqAbsorb]) from NFRel⇒orbit.
  - Part B (前者): reduce NFRel⇒orbit to ONE explicit “context+kernel completeness” lemma,
                   and use it to produce an actual NFRel⇒orbit instance.

This step does not change any previous meaning; it only tightens the boundary:
many scattered axioms become one single explicit completeness statement.
-/

section

-- ============================================================
-- Part A (後者): gap-obligations are consequences of NFRel⇒orbit
-- ============================================================

/--
If we have NFRel⇒orbit (the true content), then the two Step11 obligations follow immediately.
This is exactly Step13, but we expose it here as “Part A”.
-/
theorem gapImpliesKind_nil_ge11_of_NFRelImpliesOrbitAt
  (hNF : Step13.NFRelImpliesOrbitAt) :
  GapImpliesKindAt_nil_ge11 :=
  Step13.gapImpliesKind_nil_ge11_of_NFRelImpliesOrbitAt (hNF := hNF)

theorem gapImpliesKind_sqAbsorb_ge11_of_NFRelImpliesOrbitAt
  (hNF : Step13.NFRelImpliesOrbitAt) :
  GapImpliesKindAt_sqAbsorb_ge11 :=
  Step13.gapImpliesKind_sqAbsorb_ge11_of_NFRelImpliesOrbitAt (hNF := hNF)

/--
Bundled completion target (the exact thing Step10 wants), again as a derived consequence.
-/
theorem vars1CompletionTarget_of_NFRelImpliesOrbitAt
  (hNF : Step13.NFRelImpliesOrbitAt) :
  Vars1CompletionTarget :=
  Step13.vars1CompletionTarget_of_NFRelImpliesOrbitAt (hNF := hNF)

-- ============================================================
-- Part B (前者): reduce NFRel⇒orbit to ONE concrete completeness statement
-- ============================================================

/-!
We now define the “one lemma to prove” in the most concrete shape:

NFRel on NormalForm is just `RedEq` on underlying terms.
So NFRel⇒orbit means:

  for any normal forms x,y with RedEq x.1 y.1,
  there exists a context C such that (x.1,y.1) is obtained by plugging C
  into one of the four finite core templates:
    (A,s), (s,A), (Au,A), (A,Au).

We package that as a single proposition `NFRelImpliesCtxCoreTplVars1`.

Once this is proved (later), the rest is just plumbing:
`NFRelImpliesCtxCoreTplVars1 → NFRelImpliesOrbitAt`,
then Part A gives the gap obligations.
-/

/-- NormalForm-level “context step”: x is plug C lhs and y is plug C rhs. -/
def CtxStepNF (lhs rhs : Term V) (x y : NormalForm V) : Prop :=
  ∃ C : Ctx V, x.1 = Ctx.plug C lhs ∧ y.1 = Ctx.plug C rhs

/--
The ONE explicit completeness statement you ultimately need:

Any NFRel (RedEq) between normal forms is witnessed by plugging a single common context
into one of the finite core templates (A,s) or (Au,A) (and symmetric orientations).
-/
def NFRelImpliesCtxCoreTplVars1 : Prop :=
  ∀ x y : NormalForm V, x.1 ≠ y.1 → NFRel (α := V) x y →
    (CtxStepNF A  s  x y) ∨ (CtxStepNF s  A  x y) ∨
    (CtxStepNF Au A  x y) ∨ (CtxStepNF A  Au x y)

/--
From the concrete completeness statement to the desired NFRel⇒orbit (Vars1OrbitTpl).
This is purely definitional: orbit is “∃C,u0,v0 in core template”.
-/
theorem NFRelImpliesOrbitAt_of_NFRelImpliesCtxCoreTplVars1
  (h : NFRelImpliesCtxCoreTplVars1) :
  Step13.NFRelImpliesOrbitAt := by
  intro x y hne hRel
  have hw := h x y hne hRel
  -- unpack four cases, build Vars1OrbitTpl directly
  rcases hw with hw | hw | hw | hw
  · rcases hw with ⟨C, hx, hy⟩
    refine ⟨C, A, s, ?_, ?_, ?_⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · simp [hx]
    · simp [hy]
  · rcases hw with ⟨C, hx, hy⟩
    refine ⟨C, s, A, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · simp [hx]
    · simp [hy]
  · rcases hw with ⟨C, hx, hy⟩
    refine ⟨C, Au, A, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · simp [hx]
    · simp [hy]
  · rcases hw with ⟨C, hx, hy⟩
    refine ⟨C, A, Au, ?_, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · simp [hx]
    · simp [hy]

/-!
At this point, Step15 has completed the *structural work*:

- Part A: gap obligations follow from NFRel⇒orbit.
- Part B: NFRel⇒orbit follows from ONE explicit “context+kernel completeness” lemma.

So the entire remaining mathematics is now isolated into:

  `NFRelImpliesCtxCoreTplVars1`

Everything else is plumbing you already proved in Step0–Step14.
-/

-- ============================================================
-- Step15 “deliverables”: replace Step11's two axioms by ONE axiom
-- ============================================================

/--
SAFE boundary (one axiom instead of many):

You can now replace Step11's `gapImpliesKind_*` axioms by proving this ONE statement instead.
-/
axiom nfRelImpliesCtxCoreTplVars1 : NFRelImpliesCtxCoreTplVars1

/-- Now we get an actual NFRel⇒orbit instance. -/
theorem nfRelImpliesOrbitAt : Step13.NFRelImpliesOrbitAt :=
  NFRelImpliesOrbitAt_of_NFRelImpliesCtxCoreTplVars1 (h := nfRelImpliesCtxCoreTplVars1)

/--
Finally, the two gap obligations (the “後者”) are obtained unconditionally from the above.
These are the exact Step11 targets, now derived from a single boundary axiom.
-/
theorem gapImpliesKind_nil_ge11 : GapImpliesKindAt_nil_ge11 :=
  gapImpliesKind_nil_ge11_of_NFRelImpliesOrbitAt (hNF := nfRelImpliesOrbitAt)

theorem gapImpliesKind_sqAbsorb_ge11 : GapImpliesKindAt_sqAbsorb_ge11 :=
  gapImpliesKind_sqAbsorb_ge11_of_NFRelImpliesOrbitAt (hNF := nfRelImpliesOrbitAt)

theorem vars1CompletionTarget : Vars1CompletionTarget :=
  vars1CompletionTarget_of_NFRelImpliesOrbitAt (hNF := nfRelImpliesOrbitAt)

end

end Step15
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
