import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Rewrite

open WeakAbsorption.Closure

namespace WeakAbsorption
namespace WAA
variable {α : Type}

-- 共通前駆から左右に RedStar が伸びる「peak」-/
structure Peak (α : Type) where
  (src left right : Term α)
  (src_to_left  : RedStar (α := α) src left)
  (src_to_right : RedStar (α := α) src right)

-- peak から RedEq を作る（u ~ s ~ v）-/
theorem RedEq_of_peak {α : Type} (p : Peak α) : RedEq (α := α) p.left p.right := by
  have hl : RedEq (α := α) p.src p.left  :=
    RedEq_of_RedStar (α := α) p.src_to_left
  have hr : RedEq (α := α) p.src p.right :=
    RedEq_of_RedStar (α := α) p.src_to_right
  exact EqvGen.trans _ _ _ (EqvGen.symm _ _ hl) hr


def CtxStep (lhs rhs : Term α) (x y : NormalForm α) : Prop :=
  ∃ C : Ctx α, x.1 = Ctx.plug C lhs ∧ y.1 = Ctx.plug C rhs

theorem CtxStep_sound {lhs rhs : Term α} (h : RedEq (α := α) lhs rhs)
    {x y : NormalForm α} :
    CtxStep (α := α) lhs rhs x y → NFRel (α := α) x y := by
  rintro ⟨C, hx, hy⟩
  -- NFRel x y = RedEq x.1 y.1
  dsimp [NFRel]
  simpa [hx, hy] using (RedEq_ctx (α := α) (C := C) h)

end WAA
end WeakAbsorption
