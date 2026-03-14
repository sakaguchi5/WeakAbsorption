import WeakAbsorption.Proof.Generators.Kernel

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA

variable {α β : Type}

/-- 無向隣接：`NFStepR` の向きを忘れた版。 -/
def NFAdjR (R : RuleSet) (x y : NormalForm α) : Prop :=
  NFStepR (α := α) R x y ∨ NFStepR (α := α) R y x

theorem NFAdjR_symm (R : RuleSet) {x y : NormalForm α} :
    NFAdjR (α := α) R x y → NFAdjR (α := α) R y x := by
  intro h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- `EqvGen` の relation inclusion による単調性。 -/
theorem EqvGen_mono {r s : β → β → Prop}
    (hsub : ∀ {u v}, r u v → s u v) :
    ∀ {u v}, EqvGen r u v → EqvGen s u v := by
  intro u v h
  induction h with
  | rel a b hab =>
      exact EqvGen.rel _ _ (hsub hab)
  | refl a =>
      exact EqvGen.refl a
  | symm a b hab ih =>
      exact EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc =>
      exact EqvGen.trans _ _ _ ihab ihbc

/--
対称 relation `r` が 2 点集合 `{a,c}` を edge レベルで保つなら、
その `EqvGen r` も `{a,c}` への所属を保つ。
-/
theorem EqvGen_preserves_two_points
    {r : β → β → Prop} {a c u v : β}
    (hsymm : ∀ {x y}, r x y → r y x)
    (hclosed : ∀ x y, (x = a ∨ x = c) → r x y → (y = a ∨ y = c)) :
    EqvGen r u v → ((u = a ∨ u = c) ↔ (v = a ∨ v = c)) := by
  intro h
  induction h with
  | rel x y hxy =>
      constructor
      · intro hx
        exact hclosed x y hx hxy
      · intro hy
        exact hclosed y x hy (hsymm hxy)
  | refl x =>
      exact Iff.rfl
  | symm x y hxy ih =>
      exact ih.symm
  | trans x y z hxy hyz ihxy ihyz =>
      exact Iff.trans ihxy ihyz

/--
`a` を含む `NFEqR R`-component が実は `{a,c}` の 2 点だけなら、
その外の `z` とは `NFEqR R` で結べない。
-/
theorem not_NFEqR_of_two_point_component
    (R : RuleSet) {a c z : NormalForm α}
    (hclosed : ∀ u v, (u = a ∨ u = c) → NFAdjR (α := α) R u v → (v = a ∨ v = c))
    (hz1 : z ≠ a) (hz2 : z ≠ c) :
    ¬ NFEqR (α := α) R a z := by
  intro hEq
  have hAdj : EqvGen (NFAdjR (α := α) R) a z := by
    exact EqvGen_mono
      (β := NormalForm α)
      (r := NFStepR (α := α) R)
      (s := NFAdjR (α := α) R)
      (fun h => Or.inl h)
      hEq
  have hmem :
      (a = a ∨ a = c) ↔ (z = a ∨ z = c) := by
    exact EqvGen_preserves_two_points
      (r := NFAdjR (α := α) R)
      (a := a) (c := c)
      (u := a) (v := z)
      (fun h => NFAdjR_symm (α := α) (R := R) h)
      hclosed
      hAdj
  have hz : z = a ∨ z = c := hmem.mp (Or.inl rfl)
  cases hz with
  | inl hza => exact hz1 hza
  | inr hzc => exact hz2 hzc

theorem EqvGen_preserves_pred
    {r : β → β → Prop} {P : β → Prop} {u v : β}
    (hsymm : ∀ {x y}, r x y → r y x)
    (hclosed : ∀ x y, P x → r x y → P y) :
    EqvGen r u v → (P u ↔ P v) := by
  intro h
  induction h with
  | rel x y hxy =>
      constructor
      · intro hx
        exact hclosed x y hx hxy
      · intro hy
        exact hclosed y x hy (hsymm hxy)
  | refl x =>
      exact Iff.rfl
  | symm x y hxy ih =>
      exact ih.symm
  | trans x y z hxy hyz ihxy ihyz =>
      exact Iff.trans ihxy ihyz

theorem not_NFEqR_of_closed_pred
    (R : RuleSet) {a z : NormalForm α} {P : NormalForm α → Prop}
    (ha : P a)
    (hclosed : ∀ u v, P u → NFAdjR (α := α) R u v → P v)
    (hz : ¬ P z) :
    ¬ NFEqR (α := α) R a z := by
  intro hEq
  have hAdj : EqvGen (NFAdjR (α := α) R) a z := by
    exact EqvGen_mono
      (β := NormalForm α)
      (r := NFStepR (α := α) R)
      (s := NFAdjR (α := α) R)
      (fun h => Or.inl h)
      hEq
  have hmem : P a ↔ P z := by
    exact EqvGen_preserves_pred
      (r := NFAdjR (α := α) R)
      (P := P)
      (u := a) (v := z)
      (fun h => NFAdjR_symm (α := α) (R := R) h)
      hclosed
      hAdj
  exact hz (hmem.mp ha)


end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
