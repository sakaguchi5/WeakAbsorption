import WeakAbsorption.Core.Syntax
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Equational

namespace WeakAbsorption
open WeakAbsorption.Closure

namespace Counterexample

/-!
Counterexample:
There exist distinct normal terms u ≠ v but RedEq u v.

Concretely:
x := var a
s := x⋆x
u := s⋆s
v := s
and we show u,v are normal, u ≠ v, and u ≈ v.
-/

section
variable {α : Type} (a : α)

private def X : Term α := Term.var a
private def S : Term α := (X (a := a)) ⋆ (X (a := a))          -- x⋆x
private def V : Term α := (S (a := a)) ⋆ (X (a := a))          -- (x⋆x)⋆x
private def U : Term α := (S (a := a)) ⋆ (S (a := a))          -- (x⋆x)⋆(x⋆x)
private def T : Term α := (V (a := a)) ⋆ (S (a := a))          -- ((x⋆x)⋆x)⋆(x⋆x)

-- T → U  (C1 in the left child)
private theorem T_to_U :
  Red (α := α) (T (a := a)) (U (a := a)) := by
  have hleft :
      Red (α := α)
        ((S (a := a)) ⋆ (X (a := a)))
        (S (a := a)) := by
    exact Red.step _ _ (RedStep.C1 (X (a := a)) (X (a := a)))
  exact Red.left _ _ _ hleft

-- T → V  (C2p at root)
private theorem T_to_V :
  Red (α := α) (T (a := a)) (V (a := a)) := by
  exact Red.step _ _ (RedStep.C2p (X (a := a)) (X (a := a)) (X (a := a)))

-- V → S  (C1 at root)
private theorem V_to_S :
  Red (α := α) (V (a := a)) (S (a := a)) := by
  exact Red.step _ _ (RedStep.C1 (X (a := a)) (X (a := a)))

-- U ≈ S  (zig-zag through T and V)
private theorem RedEq_U_S :
  RedEq (U (a := a)) (S (a := a)) := by
  have eU_T : RedEq (U (a := a)) (T (a := a)) :=
    EqvGen.symm _ _ (EqvGen.rel _ _ (T_to_U (α := α) (a := a)))
  have eT_V : RedEq (T (a := a)) (V (a := a)) :=
    EqvGen.rel _ _ (T_to_V (α := α) (a := a))
  have eV_S : RedEq (V (a := a)) (S (a := a)) :=
    EqvGen.rel _ _ (V_to_S (α := α) (a := a))
  exact EqvGen.trans _ _ _ eU_T (EqvGen.trans _ _ _ eT_V eV_S)

-- ---- Normality (pattern-based, no Normal_op_iff dependency) ----

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

private theorem not_hasC1_S :
  ¬ HasC1 (S (α := α) (a := a)) := by
  simpa [S, X] using (not_hasC1_var_op_var (a1 := a) (b1 := a))

private theorem not_hasC2_S :
  ¬ HasC2p (S (α := α) (a := a)) := by
  simpa [S, X] using (not_hasC2_var_op_var (a1 := a) (b1 := a))

private theorem S_normal :
  Normal (S (α := α) (a := a)) := by
  intro w hw
  have hpat := red_implies_pattern (α := α) hw
  cases hpat with
  | inl hc1 => exact not_hasC1_S (α := α) (a := a) hc1
  | inr hc2 => exact not_hasC2_S (α := α) (a := a) hc2

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
  | inl hc1 => exact not_hasC1_U (α := α) (a := a) hc1
  | inr hc2 => exact not_hasC2_U (α := α) (a := a) hc2

-- U ≠ S (syntactic size/shape contradiction; here it reduces to var/op clash)
private theorem U_ne_S :
  U (α := α) (a := a) ≠ S (α := α) (a := a) := by
  intro h
  -- U = (x⋆x)⋆(x⋆x), S = x⋆x
  dsimp [U, S, X] at h
  injection h with h1 h2
  -- h1 : (var a ⋆ var a) = var a
  cases h1

/-- **Main packaged statement**: distinct normals but RedEq-equivalent. -/
theorem exists_distinct_normals_RedEq (a : α) :
  ∃ u v : Term α, Normal u ∧ Normal v ∧ RedEq u v ∧ u ≠ v := by
  refine ⟨U (α := α) (a := a), S (α := α) (a := a), ?_, ?_, ?_, ?_⟩
  · exact U_normal (α := α) (a := a)
  · exact S_normal (α := α) (a := a)
  · exact RedEq_U_S (α := α) (a := a)
  · exact U_ne_S (α := α) (a := a)

end
end Counterexample
end WeakAbsorption
