namespace WeakAbsorption

universe u v w

/-- 型どうしの同値（逆写像つき）: mathlib の `Equiv` 相当を最小で自前定義。 -/
structure Equiv (α : Sort _) (β : Sort _) where
  (toFun : α → β) (invFun : β → α)
  (left_inv : ∀ x, invFun (toFun x) = x)
  (right_inv : ∀ x, toFun (invFun x) = x)
/-
/-- 型どうしの同値（逆写像つき）: mathlib の `Equiv` 相当を最小で自前定義。 -/
structure Equiv (α : Sort u) (β : Sort v) : Type (max u v) where
  toFun    : α → β
  invFun   : β → α
  leftInv  : ∀ x : α, invFun (toFun x) = x
  rightInv : ∀ y : β, toFun (invFun y) = y
-/

/-
namespace Equiv

variable {α : Sort u} {β : Sort v} {γ : Sort w}

instance : CoeFun (Equiv α β) (fun _ => α → β) := ⟨Equiv.toFun⟩

def refl (α : Sort u) : Equiv α α where
  toFun    := fun x => x
  invFun   := fun x => x
  leftInv  := fun _ => rfl
  rightInv := fun _ => rfl

def symm (e : Equiv α β) : Equiv β α where
  toFun    := e.invFun
  invFun   := e.toFun
  leftInv  := e.rightInv
  rightInv := e.leftInv

def trans (e₁ : Equiv α β) (e₂ : Equiv β γ) : Equiv α γ where
  toFun    := fun x => e₂.toFun (e₁.toFun x)
  invFun   := fun z => e₁.invFun (e₂.invFun z)
  leftInv  := fun x =>
    calc e₁.invFun (e₂.invFun (e₂.toFun (e₁.toFun x)))
        = e₁.invFun (e₁.toFun x) :=
            congrArg e₁.invFun (e₂.leftInv (e₁.toFun x))
      _ = x := e₁.leftInv x
  rightInv := fun y =>
    calc e₂.toFun (e₁.toFun (e₁.invFun (e₂.invFun y)))
        = e₂.toFun (e₂.invFun y) :=
            congrArg e₂.toFun (e₁.rightInv (e₂.invFun y))
      _ = y := e₂.rightInv y

end Equiv
-/
/-- `≃` 記法を WeakAbsorption 名前空間にスコープ。
    `open WeakAbsorption` したときだけ有効になる。 -/
scoped infixl:25 " ≃ " => WeakAbsorption.Equiv

end WeakAbsorption
