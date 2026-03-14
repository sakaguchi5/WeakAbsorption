import WeakAbsorption.Core.Rewrite

namespace WeakAbsorption

/-! ############################################################
## 5. Measure infrastructure
############################################################ -/

------------------------------------------------------------
-- Size measure
------------------------------------------------------------

/-- Node-count style size (used for termination). -/
def size {α} : Term α → Nat
  | Term.var _  => 1
  | Term.op t u => size t + size u + 1

theorem size_decrease_step {α} :
  ∀ {t u : Term α}, RedStep t u → size u < size t := by
  intro t u h
  cases h with
  | C1 x y =>
      change size x + size y + 1 < (size x + size y + 1) + size y + 1
      have : 0 < size y + 1 := Nat.succ_pos _
      exact Nat.lt_add_of_pos_right this
  | C2p x y z =>
      change
        (size x + size y + 1) + size z + 1
        <
        ((size x + size y + 1) + size z + 1) + (size y + size z + 1) + 1
      have : 0 < (size y + size z + 1) + 1 := Nat.succ_pos _
      exact Nat.lt_add_of_pos_right this

theorem size_decrease {α} :
  ∀ {t u : Term α}, Red t u → size u < size t := by
  intro t u h
  induction h with
  | step _ _ hstep =>
      exact size_decrease_step hstep
  | left t₁ t₁' t₂ _ ih =>
      have : size t₁' < size t₁ := ih
      simpa [size] using Nat.add_lt_add_right this (size t₂ + 1)
  | right t₁ t₂ t₂' _ ih =>
      have : size t₂' < size t₂ := ih
      simpa [size] using Nat.add_lt_add_left this (size t₁ + 1)

------------------------------------------------------------
-- LeafCount measure
------------------------------------------------------------


/-- A second measure: leafCount (variable occurrences). -/
def leafCount : Term α → Nat
  | .var _  => 1
  | .op t u => leafCount t + leafCount u

private theorem leafCount_pos (t : Term α) : 0 < leafCount t := by
  induction t with
  | var _ =>
      exact Nat.zero_lt_one
  | op t u ih1 ih2 =>
    -- 0 < leafCount t + leafCount u を示したい
    -- Nat.add_pos は Std や Mathlib にあるが、
    -- Init の範囲なら以下のように apply で繋ぐのが確実です
    apply Nat.lt_of_lt_of_le ih1
    apply Nat.le_add_right

private theorem leafCount_decrease_step :
  ∀ {t u : Term α}, RedStep t u → leafCount u < leafCount t := by
  intro t u h
  cases h with
  | C1 x y =>
      change leafCount (Term.op x y) < leafCount (Term.op x y) + leafCount y
      exact Nat.lt_add_of_pos_right (leafCount_pos (α := α) y)
  | C2p x y z =>
      change leafCount (Term.op (Term.op x y) z)
        < leafCount (Term.op (Term.op x y) z) + leafCount (Term.op y z)
      exact Nat.lt_add_of_pos_right (leafCount_pos (α := α) (Term.op y z))

theorem leafCount_decrease :
  ∀ {t u : Term α}, Red t u → leafCount u < leafCount t := by
  intro t u h
  induction h with
  | step _ _ hstep =>
      exact leafCount_decrease_step (α := α) hstep
  | left t₁ t₁' t₂ _ ih =>
      simpa [leafCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_lt_add_right ih (leafCount t₂)
  | right t₁ t₂ t₂' _ ih =>
      simpa [leafCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_lt_add_left ih (leafCount t₁)
------------------------------------------------------------
-- Generic measure lemmas
------------------------------------------------------------

namespace Measure

variable {α : Type}

/-- Decreasing along contextual rewriting. -/
def DecreasesOnRed (μ : Term α → Nat) : Prop :=
  ∀ {t u : Term α}, Red t u → μ u < μ t

/-- Non-increasing along `RedStar`. -/
theorem le_of_star (μ : Term α → Nat)
  (hdec : DecreasesOnRed (α := α) μ)
  {t u : Term α} (h : RedStar (α := α) t u) :
  μ u ≤ μ t := by
  -- induction の際に引数名を指定すると混乱が防げます
  induction h with
  | refl =>
      exact Nat.le_refl (μ t)
  | tail h_star h_step ih =>
      -- h_star : RedStar t b (t から b への 0 回以上の書き換え)
      -- h_step : Red b c     (b から c への 1 回の書き換え)
      -- ih     : μ b ≤ μ t   (帰納法の仮定)
      -- 1. 最後の 1 ステップで値が減少することを示す
      have h_lt : μ _ < μ _ := hdec h_step -- μ c < μ b
      -- 2. μ c < μ b ≤ μ t なので推移律で解決
      exact Nat.le_trans (Nat.le_of_lt h_lt) ih

/-- If `μ` is non-increasing along `RedStar` and `μ u > μ v`, then `v →* u` is impossible. -/
theorem impossible_star
  (μ : Term α → Nat)
  (hdec : DecreasesOnRed (α := α) μ)
  {v u : Term α}
  (hgt : μ u > μ v) :
  ¬ RedStar (α := α) v u := by
  intro hvu
  have hle : μ u ≤ μ v := le_of_star (α := α) μ hdec hvu
  exact (Nat.not_succ_le_self _)
    (Nat.le_trans (Nat.succ_le_of_lt hgt) hle)

end Measure





end WeakAbsorption
