import WeakAbsorption.Core.Syntax
import WeakAbsorption.Core.Closure
--open WeakAbsorption.Closure

namespace WeakAbsorption
/-! ############################################################
## 2. Root rewrite rules (C1, C2')
############################################################ -/
inductive RedStep {α : Type} : Term α → Term α → Prop where
  | C1 : ∀ x y,
      RedStep (Term.op (Term.op x y) y) (Term.op x y)
  | C2p : ∀ x y z,
      RedStep
        (Term.op (Term.op (Term.op x y) z) (Term.op y z))
        (Term.op (Term.op x y) z)
/-! ############################################################
## 3. Context closure of rewriting
############################################################ -/

inductive Red {α : Type} : Term α → Term α → Prop where
  | step  : ∀ t u, RedStep t u → Red t u
  | left  : ∀ t₁ t₁' t₂, Red t₁ t₁' → Red (Term.op t₁ t₂) (Term.op t₁' t₂)
  | right : ∀ t₁ t₂ t₂', Red t₂ t₂' → Red (Term.op t₁ t₂) (Term.op t₁ t₂')

--Term のコンテキスト（穴あき項）
inductive Ctx (α : Type) : Type where
  | hole : Ctx α
  | left  : Ctx α → Term α → Ctx α   -- □ ⋆ r
  | right : Term α → Ctx α → Ctx α   -- l ⋆ □
deriving Repr
namespace Ctx
def plug {α} : Ctx α → Term α → Term α
    | hole, t => t
    | left C r, t => Term.op (plug C t) r
    | right l C, t => Term.op l (plug C t)
end Ctx

/-- `t` is normal iff it has no outgoing `Red` steps. -/
def Normal {α} (t : Term α) : Prop :=
 ∀ u, ¬ Red t u

/-- Reflexive-transitive closure of contextual rewriting. -/
abbrev RedStar {α} :
  Term α → Term α → Prop :=
  WeakAbsorption.Closure.ReflTransGen (@Red α)

theorem Red_to_RedStar {α} {t u : Term α} (h : Red t u) : RedStar t u :=
  WeakAbsorption.Closure.ReflTransGen.single h

-------------------------------------------

variable {α : Type}

-- C1: (t ⋆ u) が C1 の根本縮約になる条件は「t = x ⋆ u」
def IsC1Root (t u : Term α) : Prop :=
  ∃ x, t = Term.op x u

-- C2': u の形で分岐させると扱いやすい
def IsC2pRoot (t u : Term α) : Prop :=
  match u with
  | Term.op y z => ∃ x, t = Term.op (Term.op x y) z
  | _           => False

private theorem Red_root_C1 {t u : Term α} (h : IsC1Root (α := α) t u) :
  Red (Term.op t u) t := by
  rcases h with ⟨x, rfl⟩
  -- ここでゴールは Red (op (op x u) u) (op x u)
  exact Red.step _ _ (RedStep.C1 x u)

private theorem Red_root_C2 {t u : Term α} (h : IsC2pRoot (α := α) t u) :
  Red (Term.op t u) t := by
  cases u with
  | var a =>
      -- IsC2pRoot は False なので潰れる
      cases h
  | op y z =>
      -- IsC2pRoot の定義を展開して witness を取る
      dsimp [IsC2pRoot] at h
      rcases h with ⟨x, rfl⟩
      exact Red.step _ _ (RedStep.C2p x y z)

theorem Normal_op_iff (t u : Term α) :
  Normal (α := α) (Term.op t u)
    ↔ Normal (α := α) t
    ∧ Normal (α := α) u
    ∧ ¬ IsC1Root (α := α) t u
    ∧ ¬ IsC2pRoot (α := α) t u := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Normal t
      intro t' ht'
      have : Red (Term.op t u) (Term.op t' u) := Red.left _ _ _ ht'
      exact (h (Term.op t' u)) this
    · -- Normal u
      intro u' hu'
      have : Red (Term.op t u) (Term.op t u') := Red.right _ _ _ hu'
      exact (h (Term.op t u')) this
    · -- no C1 root-redex
      intro hc1
      have : Red (Term.op t u) t := Red_root_C1 (α := α) hc1
      exact (h t) this
    · -- no C2 root-redex
      intro hc2
      have : Red (Term.op t u) t := Red_root_C2 (α := α) hc2
      exact (h t) this
  · rintro ⟨ht, hu, hnc1, hnc2⟩ v hv
    cases hv with
    | left t₁ t₁' t₂ h₁ =>
        -- hv : Red t t₁' → contradiction with Normal t
        exact ht _ h₁
    | right t₁ t₂ t₂' h₂ =>
        exact hu _ h₂
    | step _ _ hs =>
        cases hs with
        | C1 x y =>
            -- ここで (Term.op t u) = ((x⋆y)⋆y) に同一化されるので
            -- t = (x⋆y), u = y が入った状態になる
            exact hnc1 ⟨x, rfl⟩
        | C2p x y z =>
            -- ここで t = ((x⋆y)⋆z), u = (y⋆z) が入った状態
            exact hnc2 (by
              dsimp [IsC2pRoot]
              exact ⟨x, rfl⟩)

-------------------------------------------





-- 既にある前提：
-- Term, Red, Normal
-- IsC1Root, IsC2pRoot
-- Normal_op_iff : Normal (op t u) ↔ Normal t ∧ Normal u ∧ ¬IsC1Root t u ∧ ¬IsC2pRoot t u

/-- Normal な項を「生成規則（文法）」として表した述語 -/
inductive NormalTerm : Term α → Prop where
  | var (a : α) : NormalTerm (Term.var a)
  | op {t u : Term α} :
      NormalTerm t →
      NormalTerm u →
      ¬ IsC1Root (α := α) t u →
      ¬ IsC2pRoot (α := α) t u →
      NormalTerm (Term.op t u)

@[simp] theorem NormalTerm_op_iff {α} (t u : Term α) :
  NormalTerm (α := α) (Term.op t u)
    ↔ NormalTerm (α := α) t
    ∧ NormalTerm (α := α) u
    ∧ ¬ IsC1Root (α := α) t u
    ∧ ¬ IsC2pRoot (α := α) t u := by
  constructor
  · intro h
    cases h with
    | op ht hu hn1 hn2 =>
      exact ⟨ht, hu, hn1, hn2⟩
  · rintro ⟨ht, hu, hn1, hn2⟩
    exact NormalTerm.op ht hu hn1 hn2

theorem Normal_iff_NormalTerm (t : Term α) :
  Normal (α := α) t ↔ NormalTerm (α := α) t := by
  induction t with
  | var a =>
      constructor
      · intro _h
        exact NormalTerm.var (α := α) a
      · intro _ht u hu
        -- var からは Red で一歩も出られない
        cases hu with
        | step _ _ hs =>
            cases hs
  | op t u iht ihu =>
      constructor
      · intro hN
        -- Term.var a からの RedStep は存在しないため、hu の cases で矛盾が示される
        have h := (Normal_op_iff (α := α) t u).1 hN
        rcases h with ⟨Nt, Nu, hnC1, hnC2⟩
        have ht : NormalTerm (α := α) t := (iht).1 Nt
        have hu : NormalTerm (α := α) u := (ihu).1 Nu
        exact NormalTerm.op ht hu hnC1 hnC2
      · intro hNT
        -- NormalTerm の構成子から Normal_op_iff を使って Normal に戻す
        cases hNT with
        | op ht hu hnC1 hnC2 =>
            have Nt : Normal (α := α) t := (iht).2 ht
            have Nu : Normal (α := α) u := (ihu).2 hu
            exact (Normal_op_iff (α := α) t u).2 ⟨Nt, Nu, hnC1, hnC2⟩



-------------------------------------------
/-! ############################################################
## 4. Pattern detection (for Normal proofs)
############################################################ -/

inductive HasC1 {α} : Term α → Prop where
  | here  : ∀ x y, HasC1 (Term.op (Term.op x y) y)
  | left  : ∀ t₁ t₂, HasC1 t₁ → HasC1 (Term.op t₁ t₂)
  | right : ∀ t₁ t₂, HasC1 t₂ → HasC1 (Term.op t₁ t₂)

inductive HasC2p {α} : Term α → Prop where
  | here  : ∀ x y z,
      HasC2p (Term.op (Term.op (Term.op x y) z) (Term.op y z))
  | left  : ∀ t₁ t₂, HasC2p t₁ → HasC2p (Term.op t₁ t₂)
  | right : ∀ t₁ t₂, HasC2p t₂ → HasC2p (Term.op t₁ t₂)

private theorem hasC1_implies_red {α} :
  ∀ {t : Term α}, HasC1 t → ∃ u, Red t u := by
  intro t h
  induction h with
  | here x y =>
      refine ⟨Term.op x y, ?_⟩
      exact Red.step _ _ (RedStep.C1 x y)
  | left t₁ t₂ _ ih =>
      rcases ih with ⟨u, hu⟩
      refine ⟨Term.op u t₂, ?_⟩
      exact Red.left _ _ _ hu
  | right t₁ t₂ _ ih =>
      rcases ih with ⟨u, hu⟩
      refine ⟨Term.op t₁ u, ?_⟩
      exact Red.right _ _ _ hu

private theorem hasC2_implies_red {α} :
  ∀ {t : Term α}, HasC2p t → ∃ u, Red t u := by
  intro t h
  induction h with
  | here x y z =>
      refine ⟨Term.op (Term.op x y) z, ?_⟩
      exact Red.step _ _ (RedStep.C2p x y z)
  | left t₁ t₂ _ ih =>
      rcases ih with ⟨u, hu⟩
      refine ⟨Term.op u t₂, ?_⟩
      exact Red.left _ _ _ hu
  | right t₁ t₂ _ ih =>
      rcases ih with ⟨u, hu⟩
      refine ⟨Term.op t₁ u, ?_⟩
      exact Red.right _ _ _ hu

theorem red_implies_pattern {α} :
  ∀ {t u : Term α}, Red t u → HasC1 t ∨ HasC2p t := by
  intro t u h
  induction h with
  | step _ _ hstep =>
      cases hstep with
      | C1 x y    => exact Or.inl (HasC1.here x y)
      | C2p x y z => exact Or.inr (HasC2p.here x y z)
  | left t₁ t₁' t₂ _ ih =>
      cases ih with
      | inl hc1 => exact Or.inl (HasC1.left _ _ hc1)
      | inr hc2 => exact Or.inr (HasC2p.left _ _ hc2)
  | right t₁ t₂ t₂' _ ih =>
      cases ih with
      | inl hc1 => exact Or.inl (HasC1.right _ _ hc1)
      | inr hc2 => exact Or.inr (HasC2p.right _ _ hc2)

theorem normal_iff_no_patterns {α} {t : Term α} :
  Normal t ↔ ¬ HasC1 t ∧ ¬ HasC2p t := by
  constructor
  · intro hn
    constructor
    · intro hc1
      rcases hasC1_implies_red hc1 with ⟨u, hu⟩
      exact hn u hu
    · intro hc2
      rcases hasC2_implies_red hc2 with ⟨u, hu⟩
      exact hn u hu
  · intro h u hu
    have hpat := red_implies_pattern (α := α) hu
    rcases h with ⟨hC1, hC2⟩
    cases hpat with
    | inl hc1 => exact hC1 hc1
    | inr hc2 => exact hC2 hc2
end WeakAbsorption
