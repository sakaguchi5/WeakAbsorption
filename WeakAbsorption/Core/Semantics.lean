import WeakAbsorption.Core.Algebra
import WeakAbsorption.Core.Quotient

namespace WeakAbsorption
/-! ############################################################
## 11. Models and semantics
############################################################ -/
namespace Term

variable {α A : Type}

def eval (S : C12Algebra A) (ρ : α → A) : Term α → A
  | .var a  => ρ a
  | .op t u => S.op (eval S ρ t) (eval S ρ u)
@[simp] theorem eval_var (S : C12Algebra A) (ρ : α → A) (a : α) :
    Term.eval S ρ (Term.var a) = ρ a := rfl

theorem eval_op (S : C12Algebra A) (ρ : α → A) (t u : Term α) :
    Term.eval S ρ (Term.op t u)
      = S.op (Term.eval S ρ t) (Term.eval S ρ u) := rfl
@[simp] theorem eval_C1
  (S : C12Algebra A) (ρ : α → A)
  (x y : Term α) :
  Term.eval S ρ ((Term.op x y).op y)
  =
  Term.eval S ρ (Term.op x y) :=
by
  exact S.C1
    (Term.eval S ρ x)
    (Term.eval S ρ y)

@[simp] theorem eval_C2
  (S : C12Algebra A) (ρ : α → A)
  (x y z : Term α) :
  Term.eval S ρ (((Term.op x y).op z).op (Term.op y z))
  =
  Term.eval S ρ ((Term.op x y).op z) :=
by
  exact S.C2p
    (Term.eval S ρ x)
    (Term.eval S ρ y)
    (Term.eval S ρ z)
end Term

namespace Semantics

variable {α A : Type}
variable (S : C12Algebra A) (ρ : α → A)

theorem eval_RedStep :
  ∀ {t u}, RedStep (α := α) t u →
    Term.eval S ρ t = Term.eval S ρ u := by
  intro t u h
  cases h with
  | C1 _ _ =>
      simp [Term.eval, S.C1]
  | C2p _ _ _ =>
      simp [Term.eval, S.C2p]
theorem eval_Red :
  ∀ {t u}, Red (α := α) t u →
    Term.eval S ρ t = Term.eval S ρ u := by
  intro t u h
  induction h with
  | step _ _ h =>
      exact eval_RedStep (S := S) (ρ := ρ) h
  | left _ _ _ _ ih =>
      simpa [Term.eval] using congrArg (fun a => S.op a _) ih
  | right _ _ _ _ ih =>
      simpa [Term.eval] using congrArg (fun b => S.op _ b) ih
theorem eval_RedEq :
  ∀ {t u}, RedEq (α := α) t u →
    Term.eval S ρ t = Term.eval S ρ u := by
  intro t u h
  induction h with
  | rel _ _ h =>
      exact eval_Red (S := S) (ρ := ρ) h
  | refl _ => rfl
  | symm _ _ _ ih =>
      exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
def evalWAA : WAA α → A :=
  Quot.lift
    (fun t => Term.eval S ρ t)
    (by
      intro t u h
      exact eval_RedEq (S := S) (ρ := ρ) h)
@[simp] theorem evalWAA_mk (t : Term α) :
  evalWAA (S := S) (ρ := ρ) (Quot.mk RedEq t : WAA α)
    = Term.eval S ρ t := rfl

end Semantics
end WeakAbsorption
