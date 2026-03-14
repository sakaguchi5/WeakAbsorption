import WeakAbsorption.Core.Syntax
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure
import WeakAbsorption.Core.Termination
import WeakAbsorption.Core.Equational
import WeakAbsorption.Core.Quotient
import WeakAbsorption.Core.Semantics
import WeakAbsorption.Core.Free

namespace WeakAbsorption
/-! ############################################################
## Counterexample: local confluence is false
############################################################ -/

namespace Counterexample

section
variable {α : Type} (a : α)

private def X : Term α := Term.var a
private def S : Term α := (X (a := a)).op (X (a := a))
private def V : Term α := (S (a := a)).op (X (a := a))
private def U : Term α := (S (a := a)).op (S (a := a))
private def T : Term α := (V (a := a)).op (S (a := a))

private theorem T_to_V : Red (α := α) (T (a := a)) (V (a := a)) := by
  exact Red.step _ _ (RedStep.C2p (X (a := a)) (X (a := a)) (X (a := a)))

private theorem T_to_U : Red (α := α) (T (a := a)) (U (a := a)) := by
  have hleft :
      Red (α := α)
        ((S (a := a)).op (X (a := a)))
        (S (a := a)) := by
    exact Red.step _ _ (RedStep.C1 (X (a := a)) (X (a := a)))
  exact Red.left _ _ _ hleft

private theorem not_hasC1_var_op_var {α} (a1 b1 : α) :
  ¬ HasC1 (Term.op (Term.var a1) (Term.var b1)) := by
  intro h
  have aux : ∀ t, HasC1 t → t = Term.op (Term.var a1) (Term.var b1) → False := by
    intro t ht eq
    cases ht with
    | here x y =>
        injection eq with eq1 eq2
        injection eq1
    | left t1 t2 hleft =>
        injection eq with eq1 eq2
        subst eq1
        cases hleft
    | right t1 t2 hright =>
        injection eq with eq1 eq2
        subst eq2
        cases hright
  exact aux _ h rfl

private theorem not_hasC2_var_op_var {α} (a1 b1 : α) :
  ¬ HasC2p (Term.op (Term.var a1) (Term.var b1)) := by
  intro h
  have aux : ∀ t, HasC2p t → t = Term.op (Term.var a1) (Term.var b1) → False := by
    intro t ht eq
    cases ht with
    | here x y z =>
        injection eq with eq1 eq2
        injection eq1
    | left t1 t2 hleft =>
        injection eq with eq1 eq2
        subst eq1
        cases hleft
    | right t1 t2 hright =>
        injection eq with eq1 eq2
        subst eq2
        cases hright
  exact aux _ h rfl

private theorem not_hasC1_U :
  ¬ HasC1 (U (α := α) (a := a)) := by
  intro h
  have aux : ∀ t, HasC1 t → t = U (α := α) (a := a) → False := by
    intro t ht eq
    cases ht with
    | here x y =>
        injection eq with eq1 eq2
        subst eq2
        injection eq1 with eq3 eq4
        injection eq4
    | left t1 t2 hleft =>
        injection eq with eq1 eq2
        subst eq1
        simpa [U, S, X] using (not_hasC1_var_op_var (a1 := a) (b1 := a) hleft)
    | right t1 t2 hright =>
        injection eq with eq1 eq2
        subst eq2
        simpa [U, S, X] using (not_hasC1_var_op_var (a1 := a) (b1 := a) hright)
  exact aux _ h rfl

private theorem not_hasC2_U :
  ¬ HasC2p (U (α := α) (a := a)) := by
  intro h
  have aux : ∀ t, HasC2p t → t = U (α := α) (a := a) → False := by
    intro t ht eq
    cases ht with
    | here x y z =>
        injection eq with eq1 eq2
        injection eq1 with eq3 eq4
        injection eq3
    | left t1 t2 hleft =>
        injection eq with eq1 eq2
        subst eq1
        simpa [U, S, X] using (not_hasC2_var_op_var (a1 := a) (b1 := a) hleft)
    | right t1 t2 hright =>
        injection eq with eq1 eq2
        subst eq2
        simpa [U, S, X] using (not_hasC2_var_op_var (a1 := a) (b1 := a) hright)
  exact aux _ h rfl

private theorem U_normal :
  Normal (U (α := α) (a := a)) := by
  intro w hw
  have hpat := red_implies_pattern (α := α) hw
  cases hpat with
  | inl hc1 => exact not_hasC1_U (a := a) hc1
  | inr hc2 => exact not_hasC2_U (a := a) hc2

/-- Local confluence is false (size-based contradiction). -/
theorem not_red_local_confluence (a : α) :
  ¬ (∀ (t u v : Term α), Red t u → Red t v → ∃ w, RedStar u w ∧ RedStar v w) := by
  intro H
  let x : Term α := Term.var a
  let s : Term α := x.op x
  let v : Term α := s.op x
  let u : Term α := s.op s
  let t : Term α := v.op s
  have ht_v : Red t v := by
    exact Red.step _ _ (RedStep.C2p x x x)
  have ht_u : Red t u := by
    have hv : Red v s := by
      exact Red.step _ _ (RedStep.C1 x x)
    exact Red.left _ _ _ hv
  rcases H t u v ht_u ht_v with ⟨w, huw, hvw⟩
  have hu_normal : Normal u := by
    simpa [u, s, x] using (U_normal (α := α) (a := a))
  have w_eq : w = u := RedStar_eq_of_Normal hu_normal huw
  have hvu : RedStar v u := by
    simpa [w_eq] using hvw
  have hdec : Measure.DecreasesOnRed (α := α) (@size α) := by
    intro t u h
    exact size_decrease (α := α) h
  have : ¬ RedStar (α := α) v u := by
    -- since size(u)=7 and size(v)=5
    apply Measure.impossible_star (α := α) (@size α) hdec
    -- show size u > size v (computed by simp)
    simp [size, u, v, s, x]
    --show (7 : Nat) > 5
  exact this hvu

/-- Local confluence is false (leafCount-based contradiction). -/
theorem not_red_local_confluence_no_size (a : α) :
  ¬ (∀ (t u v : Term α), Red t u → Red t v → ∃ w, RedStar u w ∧ RedStar v w) := by
  intro H
  let x : Term α := Term.var a
  let s : Term α := x.op x
  let v : Term α := s.op x
  let u : Term α := s.op s
  let t : Term α := v.op s
  have ht_v : Red t v := by
    exact Red.step _ _ (RedStep.C2p x x x)
  have ht_u : Red t u := by
    have hv : Red v s := by
      exact Red.step _ _ (RedStep.C1 x x)
    exact Red.left _ _ _ hv
  rcases H t u v ht_u ht_v with ⟨w, huw, hvw⟩
  have hu_normal : Normal u := by
    simpa [u, s, x] using (U_normal (α := α) (a := a))
  have w_eq : w = u := RedStar_eq_of_Normal hu_normal huw
  have hvu : RedStar v u := by
    simpa [w_eq] using hvw
  have hdec : Measure.DecreasesOnRed (α := α) leafCount := by
    intro t u h
    exact leafCount_decrease (α := α) h
  have : ¬ RedStar (α := α) v u := by
    apply Measure.impossible_star (α := α) leafCount hdec
    -- leafCount(u)=4, leafCount(v)=3
    simp [leafCount, u, v, s, x]
    --show (4 : Nat) > 3
  exact this hvu

end

end Counterexample

end WeakAbsorption
