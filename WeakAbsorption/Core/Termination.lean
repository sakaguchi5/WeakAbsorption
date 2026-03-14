import WeakAbsorption.Core.Measure
open WeakAbsorption.Closure

namespace WeakAbsorption

/-- Well-foundedness of an inverse-image relation
 (core-only replacement for Mathlib's `InvImage.wf`). -/
theorem wf_invImage
    {α β : Type}
    (f : α → β)
    {r : β → β → Prop}
    (h : WellFounded r) :
    WellFounded (fun a b : α => r (f a) (f b)) := by
  refine ⟨?_⟩
  intro a
  -- 強めの補題：`Acc r b` から、`f x = b` を満たす任意の `x` が逆像関係で `Acc`
  have liftAcc :
      ∀ b : β, Acc r b →
        ∀ x : α, f x = b → Acc (fun a b : α => r (f a) (f b)) x := by
    intro b hb
    induction hb with
    | intro b hb ih =>
        intro x hx
        refine Acc.intro x ?_
        intro y hy
        -- `hy : r (f y) (f x)` かつ `hx : f x = b`
        -- なので `f y` は `b` の predecessor
        apply ih (f y)
        · simpa [hx] using hy
        · rfl
  exact liftAcc (f a) (h.apply (f a)) a rfl

/-! ############################################################
## Termination via `size`
############################################################ -/
/--
ある関係 s が整礎であり、r が s の部分集合 (r a b → s a b) であれば、
r もまた整礎であることを示す。
-/
theorem WellFounded.mono {α : Sort u} {r s : α → α → Prop}
    (hwf : WellFounded s) (h : ∀ a b, r a b → s a b) : WellFounded r :=
  ⟨fun a =>
    -- s におけるアクセシビリティ (Acc s a) を r におけるアクセシビリティ (Acc r a) に変換
    let rec mono_acc {x} (acc_s : Acc s x) : Acc r x :=
      Acc.intro x fun y hr =>
        match acc_s with
        | Acc.intro _ ih => mono_acc (ih y (h y x hr))
    mono_acc (hwf.apply a)⟩

-- ... (WellFounded.mono の定義)

theorem Red_wellFounded {α : Type} :
  WellFounded (fun t u : Term α => Red u t) := by
  let wfNat : WellFounded (fun a b : Nat => a < b) :=
    (inferInstance : WellFoundedRelation Nat).wf

  let wfSize : WellFounded (fun t u : Term α => size t < size u) :=
    InvImage.wf size wfNat -- Init では wf_invImage ではなく InvImage.wf が一般的です

  -- wfSize を基に、Red の減少性 (size_decrease) を使って証明
  apply WellFounded.mono wfSize
  intro t u hred
  exact size_decrease hred

theorem exists_normal_form {α} (t : Term α) :
  ∃ u, RedStar t u ∧ Normal u := by
  classical
  have wf := Red_wellFounded (α := α)
  apply wf.induction (C := fun t => ∃ u, RedStar t u ∧ Normal u) t
  intro t ih
  by_cases hnorm : Normal t
  · exact ⟨t, ReflTransGen.refl, hnorm⟩
  · have : ∃ u, Red t u :=
      let ⟨u, hunot⟩ := Classical.not_forall.mp hnorm
      ⟨u, Classical.not_not.mp hunot⟩
    rcases this with ⟨u, hu⟩
    rcases ih u hu with ⟨v, huv, hnv⟩
    exact ⟨v, ReflTransGen.head hu huv, hnv⟩
/-! ############################################################
## Normal + RedStar
############################################################ -/
theorem RedStar_eq_of_Normal {α} {t w : Term α}
  (hn : Normal t)
  (h : RedStar (α := α) t w) :
  w = t := by
  induction h with
  | refl => rfl
  | tail mid hstep ih =>
      subst ih
      exfalso
      exact hn _ hstep

end WeakAbsorption
