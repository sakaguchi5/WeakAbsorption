import WeakAbsorption.Core.Equational

namespace WeakAbsorption
open WeakAbsorption.Closure

/--
(vars=1 で最初に出てくる核)
A := (u⋆u)⋆(u⋆u) について  A ≈ A⋆u  が C1,C2p だけで導ける。
（これが “右安定性” = SqStable の本体）
-/
theorem RedEq_sqStable {α : Type} (u : Term α) :
  RedEq ((u⋆u)⋆(u⋆u)) (((u⋆u)⋆(u⋆u))⋆u) :=
by
  -- abbreviations
  let s : Term α := u ⋆ u
  let A : Term α := s ⋆ s
  let t1 : Term α := (s ⋆ u) ⋆ s
  let t2 : Term α := s ⋆ u
  let t3 : Term α := (s ⋆ u) ⋆ u
  let t4 : Term α := ((s ⋆ u) ⋆ s) ⋆ u
  let v  : Term α := A ⋆ u

  -- basic C1 step: (u⋆u)⋆u → (u⋆u)
  have hC1_su : Red (s ⋆ u) s :=
    Red.step _ _ (RedStep.C1 u u)

  -- t1 → A  (C1 in the left child)
  have h1 : Red t1 A :=
    Red.left _ _ _ hC1_su

  -- t1 → t2  (C2p@root with x=y=z=u)
  have h2 : Red t1 t2 :=
    Red.step _ _ (RedStep.C2p u u u)

  -- t3 → t2  (C1@root with x:=s, y:=u)
  have h3 : Red t3 t2 :=
    Red.step _ _ (RedStep.C1 s u)

  -- t4 → t3  (lift h2 under left closure, i.e. C2p at position L)
  have h4 : Red t4 t3 :=
    Red.left _ _ _ h2

  -- t4 → v   (lift h1 under left closure, i.e. C1 at position LL)
  have h5 : Red t4 v :=
    Red.left _ _ _ h1

  -- Now build the zig-zag in RedEq (= EqvGen Red):
  -- A  ~ t1  (symm of t1→A)
  -- t1 ~ t2  (t1→t2)
  -- t2 ~ t3  (symm of t3→t2)
  -- t3 ~ t4  (symm of t4→t3)
  -- t4 ~ v   (t4→v)
  have eA_t1 : RedEq A t1 :=
    EqvGen.symm _ _ (EqvGen.rel _ _ h1)

  have e_t1_t2 : RedEq t1 t2 :=
    EqvGen.rel _ _ h2

  have e_t2_t3 : RedEq t2 t3 :=
    EqvGen.symm _ _ (EqvGen.rel _ _ h3)

  have e_t3_t4 : RedEq t3 t4 :=
    EqvGen.symm _ _ (EqvGen.rel _ _ h4)

  have e_t4_v : RedEq t4 v :=
    EqvGen.rel _ _ h5

  -- chain them
  refine EqvGen.trans _ _ _ eA_t1 ?_
  refine EqvGen.trans _ _ _ e_t1_t2 ?_
  refine EqvGen.trans _ _ _ e_t2_t3 ?_
  refine EqvGen.trans _ _ _ e_t3_t4 ?_
  exact e_t4_v

/-- 逆向き（“安定性”の見た目に合わせる）: A⋆u ≈ A -/
theorem RedEq_sqStable_right {α : Type} (u : Term α) :
  RedEq (((u⋆u)⋆(u⋆u))⋆u) ((u⋆u)⋆(u⋆u)) :=
by
  exact EqvGen.symm _ _ (RedEq_sqStable (u := u))

/-- G1: (t⋆u)⋆(u⋆u) ≈ (t⋆u)  を C1,C2p だけで導く。 -/
theorem RedEq_sqAbsorb {α : Type} (t u : Term α) :
  RedEq ((t⋆u)⋆(u⋆u)) (t⋆u) :=
by
  -- shorthand
  let Q : Term α := ((t⋆u)⋆u)⋆(u⋆u)    -- これが C2p の左辺そのもの
  let R : Term α := (t⋆u)⋆u

  -- C1: (t⋆u)⋆u -> (t⋆u)
  have hC1 : Red R (t⋆u) :=
    Red.step _ _ (RedStep.C1 t u)

  -- Q -> (t⋆u)⋆(u⋆u)  (左部分木で C1)
  have hQP : Red Q ((t⋆u)⋆(u⋆u)) :=
    Red.left _ _ _ hC1

  -- Q -> R  (C2p@root with x:=t, y:=u, z:=u)
  have hQR : Red Q R :=
    Red.step _ _ (RedStep.C2p t u u)

  -- RedEq をジグザグで合成：
  -- (t⋆u)⋆(u⋆u)  ~ Q ~ R ~ (t⋆u)
  have ePQ : RedEq ((t⋆u)⋆(u⋆u)) Q :=
    EqvGen.symm _ _ (EqvGen.rel _ _ hQP)
  have eQR : RedEq Q R :=
    EqvGen.rel _ _ hQR
  have eRt : RedEq R (t⋆u) :=
    EqvGen.rel _ _ hC1

  refine EqvGen.trans _ _ _ ePQ ?_
  refine EqvGen.trans _ _ _ eQR ?_
  exact eRt

/-- 特化：A := (u⋆u)⋆(u⋆u) は u⋆u に潰れる（“平方塊は二乗に潰れる”）。 -/
theorem RedEq_squareSquare_eq_square {α : Type} (u : Term α) :
  RedEq ((u⋆u)⋆(u⋆u)) (u⋆u) :=
by
  simpa using (RedEq_sqAbsorb (t := u) (u := u))

-- ※ あなたが通した定理（さっきのファイル）を使う想定：
-- theorem RedEq_sqStable_right {α} (u : Term α) :
--   RedEq (((u⋆u)⋆(u⋆u))⋆u) ((u⋆u)⋆(u⋆u))

theorem RedEq_Au_eq_square {α : Type} (u : Term α) :
  RedEq (((u⋆u)⋆(u⋆u))⋆u) (u⋆u) :=
by
  -- A⋆u ≈ A   (G2)
  have h1 : RedEq (((u⋆u)⋆(u⋆u))⋆u) ((u⋆u)⋆(u⋆u)) :=
    RedEq_sqStable_right (u := u)
  -- A ≈ u⋆u   (G1特化)
  have h2 : RedEq ((u⋆u)⋆(u⋆u)) (u⋆u) :=
    RedEq_squareSquare_eq_square (u := u)
  exact EqvGen.trans _ _ _ h1 h2

/--
次の段階：Ax と As を繋ぐ核。
A := (u⋆u)⋆(u⋆u) と置くと

  A⋆u  ≈  A⋆(u⋆u)

が C1 と SqStable から導ける。
-/
theorem RedEq_Au_eq_Auu {α : Type} (u : Term α) :
  RedEq (((u⋆u)⋆(u⋆u))⋆u) (((u⋆u)⋆(u⋆u))⋆(u⋆u)) :=
by
  let s : Term α := u ⋆ u
  let A : Term α := s ⋆ s

  -- (1) SqStable（あなたが通したやつ）：A⋆u ≈ A
  have h1 : RedEq (A ⋆ u) A :=
    RedEq_sqStable_right (u := u)

  -- (2) C1：A⋆s → A（root で1発）
  have hC1 : Red (A ⋆ s) A :=
    Red.step _ _ (RedStep.C1 s s)

  -- これを同値に持ち上げて A ≈ A⋆s
  have h2 : RedEq A (A ⋆ s) :=
    EqvGen.symm _ _ (EqvGen.rel _ _ hC1)

  -- 推移：A⋆u ≈ A ≈ A⋆s
  exact EqvGen.trans _ _ _ h1 h2

/--
補題：s := u⋆u, A := s⋆s のとき  s⋆A ≈ A
（A ≈ s を右合同で持ち上げるだけ）
-/
theorem RedEq_s_mul_A_eq_A {α : Type} (u : Term α) :
  RedEq ((u⋆u) ⋆ ((u⋆u)⋆(u⋆u))) ((u⋆u)⋆(u⋆u)) :=
by
  let s : Term α := u ⋆ u
  let A : Term α := s ⋆ s

  -- A ≈ s（あなたが通した G1 特化）
  have hAs : RedEq A s :=
    RedEq_squareSquare_eq_square (u := u)

  -- 右合同：s⋆A ≈ s⋆s
  have h1 : RedEq (s ⋆ A) (s ⋆ s) :=
    RedEq_op_right (t₁ := s) hAs

  -- s⋆s = A（定義展開して refl）
  have h2 : RedEq (s ⋆ s) A := by
    dsimp [A]
    exact EqvGen.refl _

  exact EqvGen.trans _ _ _ h1 h2

/--
本命：A⋆u ≈ s⋆A
（両方とも A に落ちる：SqStable と上の補題）
-/
theorem RedEq_Au_eq_s_mul_A {α : Type} (u : Term α) :
  RedEq (((u⋆u)⋆(u⋆u))⋆u) ((u⋆u)⋆((u⋆u)⋆(u⋆u))) :=
by
  let s : Term α := u ⋆ u
  let A : Term α := s ⋆ s

  -- A⋆u ≈ A（SqStable 右向き）
  have h1 : RedEq (A ⋆ u) A :=
    RedEq_sqStable_right (u := u)

  -- A ≈ s⋆A（上の補題の対称）
  have h2 : RedEq A (s ⋆ A) :=
    EqvGen.symm _ _ (RedEq_s_mul_A_eq_A (u := u))

  exact EqvGen.trans _ _ _ h1 h2

/-- ついで：逆向き（core に逆順が出るので便利） -/
theorem RedEq_s_mul_A_eq_Au {α : Type} (u : Term α) :
  RedEq ((u⋆u)⋆((u⋆u)⋆(u⋆u))) (((u⋆u)⋆(u⋆u))⋆u) :=
by
  exact EqvGen.symm _ _ (RedEq_Au_eq_s_mul_A (u := u))

/-- “square” operator -/
def sq {α : Type} (t : Term α) : Term α := t ⋆ t

/-- Congruence: a ≈ b ⇒ a² ≈ b² -/
theorem RedEq_sq_congr {α : Type} {a b : Term α} :
  RedEq a b → RedEq (sq a) (sq b) :=
by
  intro h
  -- (a⋆a) ≈ (b⋆a) ≈ (b⋆b)
  have h1 : RedEq (a ⋆ a) (b ⋆ a) := RedEq_op_left (t₂ := a) h
  have h2 : RedEq (b ⋆ a) (b ⋆ b) := RedEq_op_right (t₁ := b) h
  exact EqvGen.trans _ _ _ h1 h2

/--
Square-tower iterator:
sqPow 0 t = t
sqPow (n+1) t = sqPow n (t²)
So: sqPow 1 t = t², sqPow 2 t = t⁴, sqPow 3 t = t⁸, ...
-/
def sqPow {α : Type} : Nat → Term α → Term α
  | 0,     t => t
  | n+1,   t => sqPow n (sq t)

/--
Main collapse: for all n, sqPow (n+1) t ≈ t².
(“any height of squaring collapses back to the square”)
-/
theorem RedEq_sqPow_collapse {α : Type} (n : Nat) (t : Term α) :
    RedEq (sqPow (α := α) (n+1) t) (sq t) :=
by
  -- ここで t を汎用化（generalizing）するのがポイントです
  induction n generalizing t with
  | zero =>
      -- sqPow 1 t = t²
      simp [sqPow, sq]
  | succ n ih =>
      -- この時点での ih の型は ∀ (t : Term α), RedEq (sqPow (n+1) t) (sq t)
      -- なので、(sq t) を適用できます

      -- sqPow (n+2) t = sqPow (n+1) (sq t)
      -- ih を (sq t) に対して適用
      have ih' : RedEq (sqPow (n+1) (sq t)) (sq (sq t)) := ih (sq t)

      -- (sq (sq t)) ≈ sq t (G1公理/補題)
      have hc : RedEq (sq (sq t)) (sq t) := by
        simpa [sq] using (RedEq_squareSquare_eq_square (u := t))

      -- 推移律で結合
      -- sqPow (n+2) t = sqPow (n+1) (sq t) ≈ sq (sq t) ≈ sq t
      simp [sqPow]
      exact EqvGen.trans _ _ _ ih' hc

/--
In the “square-generated” family, everything collapses to u²:
A := u⁴ = (u²⋆u²), Au := A⋆u, As := A⋆u², sA := u²⋆A.
All are RedEq to u².
-/
theorem RedEq_square_family_collapse {α : Type} (u : Term α) :
  (RedEq ((u⋆u)⋆(u⋆u)) (u⋆u)) ∧
  (RedEq (((u⋆u)⋆(u⋆u))⋆u) (u⋆u)) ∧
  (RedEq (((u⋆u)⋆(u⋆u))⋆(u⋆u)) (u⋆u)) ∧
  (RedEq ((u⋆u)⋆((u⋆u)⋆(u⋆u))) (u⋆u)) :=
by
  -- A ≈ u²
  have hA : RedEq ((u⋆u)⋆(u⋆u)) (u⋆u) :=
    RedEq_squareSquare_eq_square (u := u)

  -- Au ≈ u²  (you already proved this earlier as RedEq_Au_eq_square)
  have hAu : RedEq (((u⋆u)⋆(u⋆u))⋆u) (u⋆u) :=
    RedEq_Au_eq_square (u := u)

  -- As ≈ Au ≈ u²
  have hAs : RedEq (((u⋆u)⋆(u⋆u))⋆(u⋆u)) (u⋆u) := by
    -- Au ≈ As  (your RedEq_Au_eq_Auu), then trans with hAu
    have hAuAs : RedEq (((u⋆u)⋆(u⋆u))⋆u) (((u⋆u)⋆(u⋆u))⋆(u⋆u)) :=
      RedEq_Au_eq_Auu (u := u)
    exact EqvGen.trans _ _ _ (EqvGen.symm _ _ hAuAs) hAu

  -- sA ≈ Au ≈ u²
  have hsA : RedEq ((u⋆u)⋆((u⋆u)⋆(u⋆u))) (u⋆u) := by
    -- sA ≈ Au  (your RedEq_s_mul_A_eq_Au), then trans with hAu
    have hsAAu : RedEq ((u⋆u)⋆((u⋆u)⋆(u⋆u))) (((u⋆u)⋆(u⋆u))⋆u) :=
      RedEq_s_mul_A_eq_Au (u := u)
    exact EqvGen.trans _ _ _ hsAAu hAu

  exact ⟨hA, ⟨hAu, ⟨hAs, hsA⟩⟩⟩

/-- `var` から始まる `Red` は存在しない（C1/C2p は lhs が op 根）。 -/
theorem noRed_from_var {α : Type} (a : α) (t : Term α) : ¬ Red (.var a) t := by
  intro h
  cases h with
  | step _ _ hs =>
      -- RedStep は C1/C2p しかないので lhs が var にはならない
      cases hs
  -- left/right は lhs が op 根なので、そもそも cases に出てこない

/-- `var` に終わる `Red` は存在しない（rhs も op 根）。 -/
theorem noRed_to_var {α : Type} (a : α) (t : Term α) : ¬ Red t (.var a) := by
  intro h
  cases h with
  | step _ _ hs =>
      -- RedStep の rhs も op 根なので var にはならない
      cases hs
  -- left/right は rhs が op 根なので、そもそも cases に出てこない

/-- 「var a であること」が t↔u で保存される、という対称な述語 -/
def PreservesVar {α : Type} (a : α) (t u : Term α) : Prop :=
  (t = .var a → u = .var a) ∧ (u = .var a → t = .var a)

/--
RedEq (= EqvGen Red) は「var a であること」を保存する。
（この形にすると symm が自然に処理できる）
-/
theorem RedEq_preserves_var {α : Type} (a : α) :
  ∀ {t u : Term α}, RedEq t u → PreservesVar a t u :=
by
  intro t u h
  induction h with
  | rel t u hred =>
      constructor
      · intro ht
        cases ht
        exact False.elim ((noRed_from_var (a := a) (t := u)) hred)
      · intro hu
        cases hu
        exact False.elim ((noRed_to_var (a := a) (t := t)) hred)
  | refl t =>
      constructor <;> intro hEq <;> exact hEq
  | symm t u _ ih =>
      -- ih : PreservesVar a t u から PreservesVar a u t は単に左右交換
      exact And.intro ih.2 ih.1
  | trans t m u _ _ ih1 ih2 =>
      -- ih1 : PreservesVar a t m, ih2 : PreservesVar a m u
      constructor
      · intro ht
        exact ih2.1 (ih1.1 ht)
      · intro hu
        exact ih1.2 (ih2.2 hu)

/-- 直系：var a と RedEq 同値なのは var a 自身だけ -/
theorem RedEq_var_iff {α : Type} (a : α) (t : Term α) :
  RedEq (.var a) t ↔ t = .var a :=
by
  constructor
  · intro h
    have P : PreservesVar a (.var a) t :=
      RedEq_preserves_var (a := a) (t := .var a) (u := t) h
    exact P.1 rfl
  · intro ht
    cases ht
    exact EqvGen.refl _

/-- 特に：var と op 根は絶対に RedEq で繋がらない -/
theorem not_RedEq_var_op {α : Type} (a : α) (l r : Term α) :
  ¬ RedEq (Term.var a) (Term.op l r) :=
by
  intro h
  have eqv : Term.op l r = Term.var a :=
    (RedEq_var_iff (a := a) (t := Term.op l r)).1 h
  cases eqv

end WeakAbsorption
