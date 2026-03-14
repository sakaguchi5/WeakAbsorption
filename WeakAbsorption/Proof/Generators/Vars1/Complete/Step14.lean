import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure
import WeakAbsorption.Tooling.SmallCheck.Phase0
import WeakAbsorption.Proof.Generators.Vars1.Complete.Step1

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Complete
namespace Step14

open WeakAbsorption
open WeakAbsorption.SmallCheck
open WeakAbsorption.Proof.Generators.Vars1.Complete.Step1

/-!
Step14: Vars=1 normal-shape tooling (pattern-based).

This step does NOT attempt a full enumeration/classification of all normal terms.
Instead it builds a proof-side “decision surface”:

- Bool detectors `hasC1b`, `hasC2pb` that look for C1/C2p patterns anywhere.
- Soundness/completeness: `hasC1b t = true ↔ HasC1 t`, similarly for C2p.
- Therefore: `Normal t ↔ hasC1b t = false ∧ hasC2pb t = false` (via normal_iff_no_patterns).
- Convenient derived lemmas that exclude typical redex-shapes from being normal.

This is the right granularity for the safe route: later steps can do proof by cases
on the Bool detectors (or on `HasC1/HasC2p`) without exploding.
-/

section
variable {α : Type} [DecidableEq α]

-- ============================================================
-- 14.1  Bool pattern detectors
-- ============================================================

/-- Detect C1-pattern anywhere: a subtree of the form `((x⋆y)⋆y)` exists. -/
def hasC1b : Term α → Bool
  | .var _ => false
  | .op t u =>
      let root : Bool :=
        match t with
        | .op _x y => decide (y = u)
        | _       => false
      (root || hasC1b t) || hasC1b u

/-- Detect C2'-pattern anywhere: a subtree of the form `(((x⋆y)⋆z)⋆(y⋆z))` exists. -/
def hasC2pb : Term α → Bool
  | .var _ => false
  | .op t u =>
      let root : Bool :=
        match t, u with
        | .op (.op _x y1) z1, .op y2 z2 => decide (y1 = y2 ∧ z1 = z2)
        | _, _ => false
      (root || hasC2pb t) || hasC2pb u

-- small Bool helper lemmas (core-only: proved by cases)
private theorem or_eq_true_iff (a b : Bool) :
  (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

private theorem or3_eq_true_iff (a b c : Bool) :
  ((a || b) || c) = true ↔ a = true ∨ b = true ∨ c = true := by
  constructor
  · intro h
    have h1 : (a || b) = true ∨ c = true := (or_eq_true_iff (a || b) c).1 h
    cases h1 with
    | inl hab =>
        have h2 : a = true ∨ b = true := (or_eq_true_iff a b).1 hab
        cases h2 with
        | inl ha => exact Or.inl ha
        | inr hb => exact Or.inr (Or.inl hb)
    | inr hc =>
        exact Or.inr (Or.inr hc)
  · intro h
    cases h with
    | inl ha =>
        have : (a || b) = true := (or_eq_true_iff a b).2 (Or.inl ha)
        exact (or_eq_true_iff (a || b) c).2 (Or.inl this)
    | inr h' =>
        cases h' with
        | inl hb =>
            have : (a || b) = true := (or_eq_true_iff a b).2 (Or.inr hb)
            exact (or_eq_true_iff (a || b) c).2 (Or.inl this)
        | inr hc =>
            exact (or_eq_true_iff (a || b) c).2 (Or.inr hc)

private theorem and_eq_true_iff (a b : Bool) :
  (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

private theorem not_eq_true_iff (b : Bool) :
  (!b) = true ↔ b = false := by
  cases b <;> simp

/-- core-only: `decide p` を Prop に戻す（simp依存を断つ） -/
private theorem decide_eq_true_iff (p : Prop) [Decidable p] :
  decide p = true ↔ p := by
  -- `Decidable p` インスタンスを直接分解して評価する
  cases inst : (inferInstance : Decidable p) with
  | isTrue hp  => simp [decide, inst, hp]
  | isFalse hn => simp [decide, inst, hn]
-- ============================================================
-- 14.2  Correctness: Bool ↔ Prop patterns
-- ============================================================

theorem hasC1b_true_iff {t : Term α} :
  hasC1b (α := α) t = true ↔ HasC1 (α := α) t := by
  induction t with
  | var a =>
      constructor
      · intro h; simp [hasC1b] at h
      · intro h; cases h
  | op t u iht ihu =>
      -- 左子の形で root 判定を分岐
      cases t with
      | var a =>
          -- root=false なので hasC1b (var⋆u)=hasC1b u
          constructor
          · intro hb
            have hb' : hasC1b (α := α) u = true := by
              simpa [hasC1b] using hb
            have hu : HasC1 (α := α) u := (ihu).1 hb'
            exact HasC1.right (α := α) (Term.var a) u hu
          · intro h
            -- この形では HasC1 は右部分木からしか来ない
            have hu : HasC1 (α := α) u := by
              cases h with
              | right _ _ hu => exact hu
              | left  _ _ hl => cases hl
            have hb' : hasC1b (α := α) u = true := (ihu).2 hu
            simpa [hasC1b] using hb'
      | op x y =>
          let root : Bool := decide (y = u)
          constructor
          · intro hb
            have hb' :
              ((root || hasC1b (α := α) (Term.op x y)) || hasC1b (α := α) u) = true := by
              simpa [hasC1b, root] using hb
            have hd :
              root = true ∨ hasC1b (α := α) (Term.op x y) = true ∨ hasC1b (α := α) u = true :=
              (or3_eq_true_iff root (hasC1b (α := α) (Term.op x y)) (hasC1b (α := α) u)).1 hb'
            cases hd with
            | inl hroot =>
                have hdec : decide (y = u) = true := by
                  simpa [root] using hroot
                have hyu : y = u := (decide_eq_true_iff (p := y = u)).1 hdec
                simpa [hyu] using (HasC1.here (α := α) x u)
            | inr hrest =>
                cases hrest with
                | inl ht =>
                    have ht' : HasC1 (α := α) (Term.op x y) := (iht).1 ht
                    exact HasC1.left (α := α) (Term.op x y) u ht'
                | inr hu =>
                    have hu' : HasC1 (α := α) u := (ihu).1 hu
                    exact HasC1.right (α := α) (Term.op x y) u hu'
          · intro h
            cases h with
            | here x' y' =>
                -- HasC1.here は Term.op (Term.op x y) u が Term.op (Term.op x' y') y' であることを要求する
                -- Leanのパターマッチングにより、このケースに入った時点で暗黙的に y = u が導かれている
                unfold hasC1b
                -- decide (y = u) が true になることを simp で解決
                simp
            | left t1 t2 h1 =>
                -- iht は (Term.op x y) に対する帰納法の仮定
                have : hasC1b (Term.op x y) = true := iht.2 h1
                unfold hasC1b
                simp [this]
            | right t1 t2 h2 =>
                -- ihu は u に対する帰納法の仮定
                have : hasC1b u = true := ihu.2 h2
                unfold hasC1b
                simp [this]

private def rootC2p (t u : Term α) : Bool :=
  match t, u with
  | .op (.op _x y1) z1, .op y2 z2 => decide (y1 = y2 ∧ z1 = z2)
  | _, _ => false

private theorem hasC2pb_op_eq (t u : Term α) :
  hasC2pb (α := α) (.op t u)
    = ((rootC2p (α := α) t u || hasC2pb (α := α) t) || hasC2pb (α := α) u) := by
  -- hasC2pb の定義が match を持ってるので、t,u を割って simp が一番安全
  cases t <;> cases u <;> simp [hasC2pb, rootC2p]

private theorem HasC2p_of_root_true {t u : Term α} :
  rootC2p (α := α) t u = true → HasC2p (α := α) (.op t u) := by
  intro hroot
  cases t with
  | var a =>
      -- rootC2p = false
      simp [rootC2p] at hroot
  | op t1 t2 =>
      cases u with
      | var b =>
          simp [rootC2p] at hroot
      | op u1 u2 =>
          -- ここでだけ rootC2p が true になり得る
          cases t1 with
          | var a =>
              simp [rootC2p] at hroot
          | op x y1 =>
              have hdec : decide (y1 = u1 ∧ t2 = u2) = true := by
                simpa [rootC2p] using hroot
              have hYZ : (y1 = u1 ∧ t2 = u2) :=
                (decide_eq_true_iff (p := (y1 = u1 ∧ t2 = u2))).1 hdec
              rcases hYZ with ⟨hy, hz⟩
              subst hy
              subst hz
              -- いま u = (y1 ⋆ t2) になっているので here が刺さる
              exact HasC2p.here (α := α) x y1 t2

private theorem hasC2pb_op_to_HasC2p
  {t u : Term α}
  (iht : hasC2pb (α := α) t = true ↔ HasC2p (α := α) t)
  (ihu : hasC2pb (α := α) u = true ↔ HasC2p (α := α) u)
  (hb : hasC2pb (α := α) (.op t u) = true) :
  HasC2p (α := α) (.op t u) := by
  -- hb を or3 に入る形に整形
  have hb' :
    ((rootC2p (α := α) t u || hasC2pb (α := α) t) || hasC2pb (α := α) u) = true := by
    simpa [hasC2pb_op_eq (α := α) t u] using hb

  have hd :
    rootC2p (α := α) t u = true
      ∨ hasC2pb (α := α) t = true
      ∨ hasC2pb (α := α) u = true :=
    (or3_eq_true_iff (rootC2p (α := α) t u) (hasC2pb (α := α) t) (hasC2pb (α := α) u)).1 hb'

  cases hd with
  | inl hroot =>
      exact HasC2p_of_root_true (α := α) (t := t) (u := u) hroot
  | inr hrest =>
      cases hrest with
      | inl ht => exact HasC2p.left  (α := α) t u (iht.1 ht)
      | inr hu => exact HasC2p.right (α := α) t u (ihu.1 hu)

private theorem HasC2p_to_hasC2pb_op
  {t u : Term α}
  (iht : hasC2pb (α := α) t = true ↔ HasC2p (α := α) t)
  (ihu : hasC2pb (α := α) u = true ↔ HasC2p (α := α) u)
  (h : HasC2p (α := α) (.op t u)) :
  hasC2pb (α := α) (.op t u) = true := by
  cases h with
  | here x y z =>
      -- ルートが C2′ パターンそのものなので rootC2p が true、ゆえに hasC2pb も true
      simp [hasC2pb]
  | left t u ht =>
      have ht' : hasC2pb (α := α) t = true := (iht).2 ht
      -- 左にあれば全体にもある（op の定義に ht' を突っ込むだけ）
      simp [hasC2pb, ht']
  | right t u hu =>
      have hu' : hasC2pb (α := α) u = true := (ihu).2 hu
      simp [hasC2pb, hu']

private theorem hasC2pb_true_iff (t : Term α) :
  hasC2pb (α := α) t = true ↔ HasC2p (α := α) t := by
  induction t with
  | var a =>
      constructor
      · intro hb
        have : False := by
          -- hasC2pb (var _) は false のはずなので矛盾
          simp [hasC2pb] at hb
        exact False.elim this
      · intro h
        -- HasC2p は var では作れない（constructor が here/left/right だけ）想定
        cases h
  | op t u iht ihu =>
      constructor
      · intro hb
        exact hasC2pb_op_to_HasC2p (α := α) (t := t) (u := u) iht ihu hb
      · intro h
        exact HasC2p_to_hasC2pb_op (α := α) (t := t) (u := u) iht ihu h
-- ============================================================
-- 14.3  Normality as “no patterns” in Bool form
-- ============================================================

/-- Bool normality predicate: no C1-pattern and no C2'-pattern anywhere. -/
def isNormalB (t : Term α) : Bool :=
  (! hasC1b (α := α) t) && (! hasC2pb (α := α) t)
private theorem hasC1b_eq_false_of_not_HasC1 {t : Term α}
  (hn : ¬ HasC1 (α := α) t) :
  hasC1b (α := α) t = false := by
  cases h : hasC1b (α := α) t with
  | false => rfl
  | true  =>
      have hc1 : HasC1 (α := α) t :=
        (hasC1b_true_iff (α := α) (t := t)).1 (by simpa using h)
      exact False.elim (hn hc1)

private theorem hasC2pb_eq_false_of_not_HasC2p {t : Term α}
  (hn : ¬ HasC2p (α := α) t) :
  hasC2pb (α := α) t = false := by
  cases h : hasC2pb (α := α) t with
  | false => rfl
  | true  =>
      have hc2 : HasC2p (α := α) t :=
        (hasC2pb_true_iff (α := α) (t := t)).1 (by simpa using h)
      exact False.elim (hn hc2)
/-- Bool criterion is equivalent to Prop Normal. -/
theorem isNormalB_iff_Normal {t : Term α} :
  isNormalB (α := α) t = true ↔ Normal (α := α) t := by
  constructor
  · intro hb
    have hb' :
      (! hasC1b (α := α) t) = true ∧ (! hasC2pb (α := α) t) = true := by
      have : ((! hasC1b (α := α) t) && (! hasC2pb (α := α) t)) = true := by
        simpa [isNormalB] using hb
      exact (and_eq_true_iff (! hasC1b (α := α) t) (! hasC2pb (α := α) t)).1 this
    have hC1false : hasC1b (α := α) t = false :=
      (not_eq_true_iff (hasC1b (α := α) t)).1 hb'.1
    have hC2false : hasC2pb (α := α) t = false :=
      (not_eq_true_iff (hasC2pb (α := α) t)).1 hb'.2
    have hno1 : ¬ HasC1 (α := α) t := by
      intro h
      have : hasC1b (α := α) t = true := (hasC1b_true_iff (α := α) (t := t)).2 h
      have : False := by simp [hC1false] at this
      exact this.elim
    have hno2 : ¬ HasC2p (α := α) t := by
      intro h
      have : hasC2pb (α := α) t = true := (hasC2pb_true_iff (α := α) (t := t)).2 h
      have : False := by simp [hC2false] at this
      exact this.elim
    exact (normal_iff_no_patterns (α := α) (t := t)).2 ⟨hno1, hno2⟩
  · intro hN
    have hnp : (¬ HasC1 (α := α) t) ∧ (¬ HasC2p (α := α) t) :=
      (normal_iff_no_patterns (α := α) (t := t)).1 hN
    have hC1false : hasC1b (α := α) t = false :=
      hasC1b_eq_false_of_not_HasC1 (α := α) (t := t) hnp.1
    have hC2false : hasC2pb (α := α) t = false :=
      hasC2pb_eq_false_of_not_HasC2p (α := α) (t := t) hnp.2
    have hn1 : (! hasC1b (α := α) t) = true :=
      (not_eq_true_iff (hasC1b (α := α) t)).2 hC1false
    have hn2 : (! hasC2pb (α := α) t) = true :=
      (not_eq_true_iff (hasC2pb (α := α) t)).2 hC2false
    have : ((! hasC1b (α := α) t) && (! hasC2pb (α := α) t)) = true :=
      (and_eq_true_iff (! hasC1b (α := α) t) (! hasC2pb (α := α) t)).2 ⟨hn1, hn2⟩
    simpa [isNormalB] using this

theorem not_Normal_of_hasC1b_true {t : Term α} :
  hasC1b (α := α) t = true → ¬ Normal (α := α) t := by
  intro hC1 hN
  have hB : isNormalB (α := α) t = true :=
    (isNormalB_iff_Normal (α := α) (t := t)).2 hN
  simp [isNormalB, hC1] at hB

theorem not_Normal_of_hasC2pb_true {t : Term α} :
  hasC2pb (α := α) t = true → ¬ Normal (α := α) t := by
  intro hC2 hN
  have hB : isNormalB (α := α) t = true :=
    (isNormalB_iff_Normal (α := α) (t := t)).2 hN
  simp [isNormalB, hC2] at hB

end

-- ============================================================
-- 14.4  Vars=1 convenience consequences (shape exclusion lemmas)
-- ============================================================

section
open WeakAbsorption.SmallCheck

/-- In vars=1, `Normal t` implies no patterns (re-exported form). -/
theorem normal_no_patterns_vars1 {t : Term V} :
  Normal (α := V) t → (¬ HasC1 (α := V) t ∧ ¬ HasC2p (α := V) t) := by
  intro h
  exact (normal_iff_no_patterns (α := V) (t := t)).1 h

/-- The canonical C1-shape is never normal. -/
theorem not_normal_C1shape (x y : Term V) :
  ¬ Normal (α := V) (((x ⋆ y) ⋆ y)) := by
  intro hN
  have hnp := normal_no_patterns_vars1 (t := ((x ⋆ y) ⋆ y)) hN
  exact hnp.1 (HasC1.here (α := V) x y)

/-- The canonical C2'-shape is never normal. -/
theorem not_normal_C2shape (x y z : Term V) :
  ¬ Normal (α := V) ((((x ⋆ y) ⋆ z) ⋆ (y ⋆ z))) := by
  intro hN
  have hnp := normal_no_patterns_vars1 (t := (((x ⋆ y) ⋆ z) ⋆ (y ⋆ z))) hN
  exact hnp.2 (HasC2p.here (α := V) x y z)

/--
Root-local consequence (often useful when you destruct an op-term):

If `Normal (t⋆u)` then the root is neither a C1-root nor a C2p-root.
(This is already in `Normal_op_iff`, but in a convenient lemma form.)
-/
theorem normal_op_no_roots {t u : Term V} :
  Normal (α := V) (t ⋆ u) → (¬ IsC1Root (α := V) t u ∧ ¬ IsC2pRoot (α := V) t u) := by
  intro hN
  have h := (Normal_op_iff (α := V) t u).1 hN
  exact ⟨h.2.2.1, h.2.2.2⟩

/--
A concrete “shape restriction” derived from C1-avoidance:

If `Normal (((a⋆b)⋆c))` then `b ≠ c`.
-/
theorem normal_no_dup_right {a b c : Term V} :
  Normal (α := V) ((a ⋆ b) ⋆ c) → b ≠ c := by
  intro hN hEq
  -- if b=c, the term is exactly the C1-shape ((a⋆b)⋆b)
  have : ¬ Normal (α := V) (((a ⋆ b) ⋆ b)) := not_normal_C1shape (x := a) (y := b)
  -- rewrite by hEq
  exact this (by simpa [hEq] using hN)

end

end Step14
end Complete
end Vars1
end Generators
end Proof
end WeakAbsorption
