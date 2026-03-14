import WeakAbsorption.Core.Algebra
import WeakAbsorption.Core.Quotient
import WeakAbsorption.Core.Semantics
/-! ############################################################
## Free C12Algebra structure on WAA
############################################################ -/
namespace WeakAbsorption

namespace FreeWAA

variable {α A : Type} (S : C12Algebra A) (ρ : α → A)
/-- The universal homomorphism `WAA α → S`. -/
def liftHom : C12Algebra.Hom (WAA.c12Alg α) S :=
{ toFun := Semantics.evalWAA (S := S) (ρ := ρ)
  map_op := by
    intro x y
    -- 1つ目の引数 x を持ち上げる
    refine Quot.inductionOn x ?_
    intro tx
    -- 2つ目の引数 y を持ち上げる
    refine Quot.inductionOn y ?_
    intro ty
    -- これで tx, ty : Term α のレベルで計算できる
    simpa using Term.eval_op S ρ tx ty
}
@[simp] theorem liftHom_mk (t : Term α) :
  liftHom (S := S) (ρ := ρ) (Quot.mk RedEq t : WAA α)
    = Term.eval S ρ t := by
  rfl

@[simp] theorem liftHom_eta (a : α) :
  liftHom (S := S) (ρ := ρ) (WAA.eta a) = ρ a := by
  simp [WAA.eta]

/-- Uniqueness: any homomorphism agreeing on generators is `liftHom`. -/
theorem liftHom_unique
    (f : C12Algebra.Hom (WAA.c12Alg α) S)
    (hf : ∀ a, f (WAA.eta a) = ρ a) :
    f = liftHom S ρ := by
  ext x
  refine Quot.inductionOn x ?_
  intro t
  -- f (mk t) = Term.eval S ρ t を示す have
  have ht : f (Quot.mk RedEq t : WAA α) = Term.eval S ρ t := by
    induction t with
    | var a =>
      -- f (mk a) = f (eta a) = ρ a = eval a
      rw [← WAA.eta_def, hf, Term.eval_var]
    | op t₁ t₂ ih₁ ih₂ =>
      -- f (mk (t₁ * t₂)) = f (mk t₁ * mk t₂) = f(mk t₁) op f(mk t₂) = eval t₁ op eval t₂
      -- f.map_op を使うため、一度 WAA の乗算 (*) に直す
      have hmk : (Quot.mk RedEq (Term.op t₁ t₂) : WAA α) =
          (Quot.mk RedEq t₁ : WAA α) * (Quot.mk RedEq t₂ : WAA α) := by
        rw [← WAA.mk_mul_mk t₁ t₂]
        -- WAA.mk_mul_mk を simp で適用

      -- calc の代わりに simp [hmk, f.map_op, ih₁, ih₂, Term.eval_op] でも可
      calc
        f (Quot.mk RedEq (Term.op t₁ t₂))
          = f ((Quot.mk RedEq t₁ : WAA α) * Quot.mk RedEq t₂) := by
            rw [hmk]
        _ = S.op (Term.eval S ρ t₁) (Term.eval S ρ t₂) := by
            simpa [ih₁, ih₂] using
              f.map_op (Quot.mk RedEq t₁ : WAA α)
                       (Quot.mk RedEq t₂ : WAA α)
        _ = Term.eval S ρ (Term.op t₁ t₂) := rfl
  -- 最後に liftHom_mk を使って ht と繋げる
  -- simp [liftHom_mk] を使えば、右辺の liftHom (mk t) が eval t になり、ht で終わります
  simp [liftHom_mk, ht]

/-
Freeness in `∃!` form.
theorem isFree :
  ∃! f : C12Algebra.Hom (WAA.c12Alg α) S,
    ∀ a : α, f (WAA.eta a) = ρ a :=
  ⟨liftHom S ρ, fun _ => rfl, fun f hf => liftHom_unique S ρ f hf⟩
-/

/- Freeness in ∃! form (Mathlibなし版) -/
/-- 存在と一意性を手動で分離して記述 -/
theorem isFree :
  (∃ f : C12Algebra.Hom (WAA.c12Alg α) S, ∀ a : α, f (WAA.eta a) = ρ a) ∧
  (∀ f₁ f₂ : C12Algebra.Hom (WAA.c12Alg α) S,
    (∀ a, f₁ (WAA.eta a) = ρ a) → (∀ a, f₂ (WAA.eta a) = ρ a) → f₁ = f₂) :=
  ⟨⟨liftHom S ρ, fun _ => rfl⟩, fun f₁ f₂ h1 h2 =>
    (liftHom_unique S ρ f₁ h1).trans (liftHom_unique S ρ f₂ h2).symm⟩

end FreeWAA
end WeakAbsorption
