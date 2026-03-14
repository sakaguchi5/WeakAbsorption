import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Rewrite
/-!
LAYER: GENERATORS (experimental step systems on NormalForm)
MAY import: Canonical + Rewrite (Ctx)
MUST NOT import: Semantics / Free / Universal / Completeness
Rule: only prove soundness (… → NFRel). Do not silently turn this into a “complete” theory.
-/
open WeakAbsorption.Closure
namespace WeakAbsorption
namespace WAA
variable {α : Type}

theorem RedEq_absorb_sq_right (t u : Term α) :
  RedEq ((t.op u).op (u.op u)) (t.op u) := by
  -- 共通の上流項
  let s : Term α := (((t.op u).op u).op (u.op u))
  -- s →* ((t u) (u u))  （左部分木に C1）
  have hs1 : RedStar (α := α) s ((t.op u).op (u.op u)) := by
    refine ReflTransGen.single ?_
    exact Red.left _ _ _ (Red.step _ _ (RedStep.C1 t u))
  -- s →* (t u) （ルートに C2'、さらに C1）
  have hs2 : RedStar (α := α) s (t.op u) := by
    have h1 : Red (α := α) s ((t.op u).op u) :=
      Red.step _ _ (RedStep.C2p t u u)
    have h1s : RedStar (α := α) s ((t.op u).op u) :=
      ReflTransGen.single h1
    have h2 : Red (α := α) ((t.op u).op u) (t.op u) :=
      Red.step _ _ (RedStep.C1 t u)
    exact ReflTransGen.tail h1s h2
  -- 共通上流から RedEq を作る
  have h1 : RedEq s ((t.op u).op (u.op u)) := RedEq_of_RedStar (α := α) hs1
  have h2 : RedEq s (t.op u) := RedEq_of_RedStar (α := α) hs2
  exact EqvGen.trans _ _ _ (EqvGen.symm _ _ h1) h2

theorem mul_absorb_sq_right (a b : WAA α) :
  (a * b) * (b * b) = a * b := by
  induction a using Quot.ind
  case mk t =>
    induction b using Quot.ind
    case mk u =>
      -- mk_mul_mk がある前提で simp すれば Term の形に落ちる
      simp only [mk_mul_mk]
      apply Quot.sound
      exact RedEq_absorb_sq_right (α := α) (t := t) (u := u)

def NFSqStep (x y : NormalForm α) : Prop :=
  ∃ t u : Term α,
    x.1 = ((t.op u).op (u.op u)) ∧
    y.1 = (t.op u)

theorem NFSqStep_imp_NFRel (x y : NormalForm α) :
  NFSqStep (α := α) x y → NFRel (α := α) x y := by
  rintro ⟨t, u, hx, hy⟩
  -- NFRel の定義は RedEq x.1 y.1 なので、中身の等号を代入する
  rw [NFRel]
  -- x.1 と y.1 を具体的な Term の形（t, u を使った形）に書き換える
  rw [hx, hy]
  -- 先ほど証明した Term レベルの補題を適用
  exact RedEq_absorb_sq_right (α := α) t u

theorem RedEq_absorb_sq_right_ctxR (t u r : Term α) :
  RedEq (Term.op ((t.op u).op (u.op u)) r) (Term.op (t.op u) r) := by
  -- 左引数が RedEq なら op 左側で保たれる
  apply RedEq_op_left (α := α) (t₂ := r)
  exact RedEq_absorb_sq_right (α := α) (t := t) (u := u)

theorem RedEq_absorb_sq_right_ctxL (l t u : Term α) :
  RedEq (Term.op l ((t.op u).op (u.op u))) (Term.op l (t.op u)) := by
  -- 右引数が RedEq なら op 右側で保たれる
  apply RedEq_op_right (α := α) (t₁ := l)
  exact RedEq_absorb_sq_right (α := α) (t := t) (u := u)



theorem RedEq_absorb_sq_right_ctx (C : Ctx α) (t u : Term α) :
  RedEq (Ctx.plug C ((t.op u).op (u.op u)))
        (Ctx.plug C (t.op u)) := by
  apply RedEq_ctx (α := α) (C := C)
  exact RedEq_absorb_sq_right (α := α) (t := t) (u := u)

--文脈（Ctx）内での平方吸収ステップが NFRel（RedEq 同値）を導く
theorem NFSqStepCtx_imp_NFRel {α : Type} {x y : NormalForm α} :
  NFSqStepCtx x y → NFRel (α := α) x y := by
  -- 1) NFSqStepCtx の定義に基づき、文脈 C と項 t, u を取り出す
  rintro ⟨C, t, u, hx, hy⟩
  -- 2) NFRel の定義 (RedEq x.1 y.1) を展開する
  rw [NFRel]
  -- 3) x.1 と y.1 を具体的な文脈プラグの形に置き換える
  rw [hx, hy]
  -- 4) RedEq_ctx を適用して、文脈の中身の同値性に帰着させる
  -- 目標: RedEq ((t.op u).op (u.op u)) (t.op u)
  apply RedEq_ctx
  -- 5) 既に証明済みの平方吸収の基本補題を適用する
  exact RedEq_absorb_sq_right t u
--平方吸収ステップを反射対称推移閉包したもの
def NFSqEq {α : Type} (x y : NormalForm α) : Prop :=
  EqvGen (NFSqStepCtx (α := α)) x y
--平方吸収（文脈込み）で生成される同値 ⊆ NFRel
theorem NFSqEq_imp_NFRel {α : Type} {x y : NormalForm α} :
  NFSqEq (α := α) x y → NFRel (α := α) x y := by
  intro h
  induction h with
  | rel a b hab =>
      exact NFSqStepCtx_imp_NFRel (α := α) hab
  | refl a =>
      -- NFRel a a = RedEq a.1 a.1
      exact (EqvGen.refl (r := @Red α) a.1)
  | symm a b _ ih =>
      exact (EqvGen.symm (r := @Red α) _ _ ih)
  | trans a b c _ _ ih1 ih2 =>
      exact (EqvGen.trans (r := @Red α) _ _ _ ih1 ih2)

-- A := (t⋆u)⋆(u⋆u) は右から u を掛けても同値（A⋆u ≈ A）。-/
theorem RedEq_sq_right_stable (t u : Term α) :
  RedEq (((t.op u).op (u.op u)).op u) ((t.op u).op (u.op u)) := by
  -- 記号を置く
  let A : Term α := (t.op u).op (u.op u)
  -- A ≈ (t⋆u) （平方吸収）
  have hA : RedEq A (t.op u) := by
    simpa [A] using (RedEq_absorb_sq_right (α := α) (t := t) (u := u))
  -- (A⋆u) ≈ ((t⋆u)⋆u) （左の合同性）
  have hAu : RedEq (A.op u) ((t.op u).op u) := by
    -- RedEq_op_left : RedEq A (t⋆u) → RedEq (A⋆u) ((t⋆u)⋆u)
    simpa [A] using (RedEq_op_left (α := α) (t₂ := u) hA)
  -- ((t⋆u)⋆u) → (t⋆u) （C1 の1ステップ）なので RedEq
  have hC1 : RedEq ((t.op u).op u) (t.op u) := by
    exact EqvGen.rel _ _ (Red.step _ _ (RedStep.C1 t u))
  -- A⋆u ≈ t⋆u
  have hAu' : RedEq (A.op u) (t.op u) :=
    EqvGen.trans _ _ _ hAu hC1
  -- A⋆u ≈ t⋆u かつ A ≈ t⋆u なので A⋆u ≈ A
  exact EqvGen.trans _ _ _ hAu' (EqvGen.symm _ _ hA)

theorem RedEq_sq_right_stable_ctx (C : Ctx α) (t u : Term α) :
  RedEq (Ctx.plug C (((t.op u).op (u.op u)).op u))
        (Ctx.plug C ((t.op u).op (u.op u))) := by
  apply RedEq_ctx (α := α) (C := C)
  exact RedEq_sq_right_stable (α := α) (t := t) (u := u)

/-- NormalForm 上の「平方吸収の安定化」ステップ（文脈込み）：A⋆u ≈ A -/
def NFSqStableStepCtx {α : Type} (x y : NormalForm α) : Prop :=
  ∃ (C : Ctx α) (t u : Term α),
    x.1 = Ctx.plug C ((((t.op u).op (u.op u)).op u)) ∧
    y.1 = Ctx.plug C ((t.op u).op (u.op u))

theorem NFSqStableStepCtx_imp_NFRel {α : Type} {x y : NormalForm α} :
  NFSqStableStepCtx (α := α) x y → NFRel (α := α) x y := by
  rintro ⟨C, t, u, hx, hy⟩
  -- 1) NFRel の定義を展開して RedEq x.1 y.1 にする
  rw [NFRel]
  -- 2) x.1 と y.1 を具体的な文脈プラグの形に書き換える
  rw [hx, hy]
  -- 3) 文脈内での安定性を示す補題を適用
  exact RedEq_sq_right_stable_ctx (α := α) C t u

def NFSqGenStepCtx {α : Type} (x y : NormalForm α) : Prop :=
  NFSqStepCtx (α := α) x y ∨ NFSqStableStepCtx (α := α) x y

def NFSqGenEq {α : Type} (x y : NormalForm α) : Prop :=
  EqvGen (NFSqGenStepCtx (α := α)) x y
--（平方吸収）＋（平方吸収の右安定）で生成される同値⊆NFRel
theorem NFSqGenEq_imp_NFRel {α : Type} {x y : NormalForm α} :
  NFSqGenEq (α := α) x y → NFRel (α := α) x y := by
  intro h
  induction h with
  | rel a b hab =>
      cases hab with
      | inl h0 => exact NFSqStepCtx_imp_NFRel (α := α) h0
      | inr h1 => exact NFSqStableStepCtx_imp_NFRel (α := α) h1
  | refl a =>
      exact EqvGen.refl (r := @Red α) a.1
  | symm a b _ ih =>
      exact EqvGen.symm (r := @Red α) _ _ ih
  | trans a b c _ _ ih1 ih2 =>
      exact EqvGen.trans (r := @Red α) _ _ _ ih1 ih2

theorem RedEq_C2C1_right (x p z : Term α) :
  RedEq (((x.op (p.op z)).op z).op (p.op z))
        ((x.op (p.op z)).op z) := by
  let y : Term α := p.op z
  let A : Term α := (x.op y).op z
  let s : Term α := A.op (y.op z)
  -- s -> A  (C2' at root)
  have hsA : RedEq s A := by
    exact EqvGen.rel _ _ (Red.step _ _ (RedStep.C2p x y z))
  -- s -> A⋆y  (right step with C1 on y⋆z = (p⋆z)⋆z -> p⋆z)
  have hsAy : RedEq s (A.op y) := by
    -- y⋆z -> y
    have hC1 : Red (α := α) (y.op z) y := by
      dsimp [y]
      exact Red.step _ _ (RedStep.C1 p z)
    exact EqvGen.rel _ _ (Red.right A (y.op z) y hC1)
  -- A⋆y ~ A via common predecessor s
  exact EqvGen.trans _ _ _ (EqvGen.symm _ _ hsAy) hsA

theorem RedEq_C2C1_right_ctx (C : Ctx α) (x p z : Term α) :
  RedEq (Ctx.plug C (((x.op (p.op z)).op z).op (p.op z)))
        (Ctx.plug C ((x.op (p.op z)).op z)) := by
  apply RedEq_ctx (α := α) (C := C)
  exact RedEq_C2C1_right (α := α) (x := x) (p := p) (z := z)
/-- NormalForm 上の C2'×C1 由来の生成ステップ（文脈込み） -/
def NFC2C1StepCtx {α : Type} (x y : NormalForm α) : Prop :=
  ∃ (C : Ctx α) (x0 p z : Term α),
    x.1 = Ctx.plug C (((x0.op (p.op z)).op z).op (p.op z)) ∧
    y.1 = Ctx.plug C ((x0.op (p.op z)).op z)

theorem NFC2C1StepCtx_imp_NFRel {α : Type} {x y : NormalForm α} :
  NFC2C1StepCtx (α := α) x y → NFRel (α := α) x y := by
  rintro ⟨C, x0, p, z, hx, hy⟩
  rw[NFRel]
  rw [hx, hy]
  exact RedEq_C2C1_right_ctx (α := α) (C := C) (x := x0) (p := p) (z := z)

/-- （新・生成元） (t⋆u)⋆(u⋆(u⋆u)) は (t⋆u) と RedEq 同値。 -/
theorem RedEq_decor_uuu (t u : Term α) :
  RedEq ((t.op u).op (u.op (u.op u))) (t.op u) := by
  -- 記号
  let tu : Term α := t.op u
  let uu : Term α := u.op u
  let R  : Term α := u.op uu
  -- 共通の上流項 s
  let s  : Term α := (((tu.op u).op uu).op R)
  -- s →* (t⋆u)
  have hs_tu : RedStar (α := α) s tu := by
    -- 1) ルートで C2'（x:=tu, y:=u, z:=uu）
    have h1 : Red (α := α) s ((tu.op u).op uu) :=
      Red.step _ _ (RedStep.C2p tu u uu)
    have h1s : RedStar (α := α) s ((tu.op u).op uu) :=
      ReflTransGen.single h1
    -- 2) ルートで C2'（x:=t, y:=u, z:=u）
    have h2 : Red (α := α) ((tu.op u).op uu) (tu.op u) :=
      Red.step _ _ (RedStep.C2p t u u)
    have h2s : RedStar (α := α) s (tu.op u) :=
      ReflTransGen.tail h1s h2
    -- 3) ルートで C1
    have h3 : Red (α := α) (tu.op u) tu :=
      Red.step _ _ (RedStep.C1 t u)
    exact ReflTransGen.tail h2s h3
  -- s →* ((t⋆u)⋆(u⋆(u⋆u)))  （左側だけ潰す）
  have hs_v : RedStar (α := α) s (tu.op R) := by
    -- 左部分木に C2'（x:=t, y:=u, z:=u）
    have h4 : Red (α := α) s ((tu.op u).op R) :=
      Red.left _ _ _ (Red.step _ _ (RedStep.C2p t u u))
    have h4s : RedStar (α := α) s ((tu.op u).op R) :=
      ReflTransGen.single h4
    -- 左部分木に C1
    have h5 : Red (α := α) ((tu.op u).op R) (tu.op R) :=
      Red.left _ _ _ (Red.step _ _ (RedStep.C1 t u))
    exact ReflTransGen.tail h4s h5
  -- 共通上流から RedEq を作る
  have htu : RedEq s tu := RedEq_of_RedStar (α := α) (t := s) (u := tu) hs_tu
  have hv  : RedEq s (tu.op R) := RedEq_of_RedStar (α := α) (t := s) (u := tu.op R) hs_v
  exact EqvGen.trans _ _ _ (EqvGen.symm _ _ hv) htu

theorem RedEq_decor_uuu_ctx (C : Ctx α) (t u : Term α) :
  RedEq (Ctx.plug C ((t.op u).op (u.op (u.op u))))
        (Ctx.plug C (t.op u)) := by
  apply RedEq_ctx (α := α) (C := C)
  exact RedEq_decor_uuu (α := α) (t := t) (u := u)

/-- NormalForm 上の「装飾除去」ステップ（文脈込み） -/
def NFDecorStepCtx {α : Type} (x y : NormalForm α) : Prop :=
  ∃ (C : Ctx α) (t u : Term α),
    x.1 = Ctx.plug C ((t.op u).op (u.op (u.op u))) ∧
    y.1 = Ctx.plug C (t.op u)

theorem NFDecorStepCtx_imp_NFRel {α : Type} {x y : NormalForm α} :
  NFDecorStepCtx (α := α) x y → NFRel (α := α) x y := by
  rintro ⟨C, t, u, hx, hy⟩
  rw[NFRel]
  rw [hx, hy]
  exact RedEq_decor_uuu_ctx (α := α) (C := C) (t := t) (u := u)

/-- （新・生成元, G5）
    uu := u⋆u とおくと (t⋆(uu⋆uu))⋆uu ≈ t⋆uu -/
theorem RedEq_absorb_doubleSq_right (t u : Term α) :
  RedEq ((t.op ((u.op u).op (u.op u))).op (u.op u)) (t.op (u.op u)) := by
  let uu : Term α := u.op u
  let u4 : Term α := uu.op uu
  let X  : Term α := (uu.op u).op uu
  let s  : Term α := (t.op X).op uu
  let lhs : Term α := (t.op u4).op uu
  let rhs : Term α := t.op uu
  -- s →* lhs（X の左側で C1: (uu⋆u)→uu を使って X→u4）
  have hs_lhs : RedStar (α := α) s lhs := by
    refine ReflTransGen.single ?_
    have h1 : Red (α := α) (uu.op u) uu := by
      -- (u⋆u)⋆u → (u⋆u)
      dsimp [uu]
      exact Red.step _ _ (RedStep.C1 u u)
    have hX : Red (α := α) X u4 := by
      -- ( (uu⋆u)⋆uu ) → ( uu⋆uu )
      dsimp [X, u4]
      exact Red.left _ _ _ h1
    have h2 : Red (α := α) (t.op X) (t.op u4) :=
      Red.right _ _ _ hX
    -- 外側へ lift
    dsimp [s, lhs]
    exact Red.left _ _ _ h2
  -- s →* rhs（X を C2'→C1 で uu に落としてから外側 C1）
  have hs_rhs : RedStar (α := α) s rhs := by
    let s1 : Term α := (t.op (uu.op u)).op uu
    let s2 : Term α := (t.op uu).op uu
    have hX1 : Red (α := α) X (uu.op u) := by
      -- ((u⋆u)⋆u)⋆(u⋆u) → (u⋆u)⋆u （C2'）
      dsimp [X, uu]
      exact Red.step _ _ (RedStep.C2p u u u)
    have hS1 : Red (α := α) s s1 := by
      dsimp [s, s1]
      apply Red.left _ _ _
      exact Red.right _ _ _ hX1
    have hX2 : Red (α := α) (uu.op u) uu := by
      dsimp [uu]
      exact Red.step _ _ (RedStep.C1 u u)
    have hS2 : Red (α := α) s1 s2 := by
      dsimp [s1, s2]
      apply Red.left _ _ _
      exact Red.right _ _ _ hX2
    have hS3 : Red (α := α) s2 rhs := by
      -- ((t⋆uu)⋆uu) → (t⋆uu)
      dsimp [s2, rhs]
      exact Red.step _ _ (RedStep.C1 t uu)
    -- 3ステップをつなぐ
    exact ReflTransGen.tail (ReflTransGen.tail (ReflTransGen.single hS1) hS2) hS3
  -- 共通上流 s から RedEq を作る
  have h1 : RedEq s lhs := RedEq_of_RedStar (α := α) hs_lhs
  have h2 : RedEq s rhs := RedEq_of_RedStar (α := α) hs_rhs
  exact EqvGen.trans _ _ _ (EqvGen.symm _ _ h1) h2

theorem RedEq_absorb_doubleSq_right_ctx (C : Ctx α) (t u : Term α) :
  RedEq (Ctx.plug C ((t.op ((u.op u).op (u.op u))).op (u.op u)))
        (Ctx.plug C (t.op (u.op u))) := by
  apply RedEq_ctx (α := α) (C := C)
  exact RedEq_absorb_doubleSq_right (α := α) (t := t) (u := u)

/-- NormalForm 上の G5 ステップ（文脈込み） -/
def NFDoubleSqStepCtx {α : Type} (x y : NormalForm α) : Prop :=
  ∃ (C : Ctx α) (t u : Term α),
    x.1 = Ctx.plug C ((t.op ((u.op u).op (u.op u))).op (u.op u)) ∧
    y.1 = Ctx.plug C (t.op (u.op u))

theorem NFDoubleSqStepCtx_imp_NFRel {α : Type} {x y : NormalForm α} :
  NFDoubleSqStepCtx (α := α) x y → NFRel (α := α) x y := by
  rintro ⟨C, t, u, hx, hy⟩
  rw [NFRel]
  rw [hx, hy]
  exact RedEq_absorb_doubleSq_right_ctx (α := α) (C := C) (t := t) (u := u)
----------------------------------------
--DoubleSq は「1回の発見で無限列が確定する」タイプ
----------------------------------------
--二乗塔 pow2Sq（u², u⁴, u⁸, …）
def pow2Sq {α : Type} : Nat → Term α → Term α
  | 0, u => u.op u
  | n+1, u =>
      let v := pow2Sq n u
      v.op v
--“吸収”の無限列（u^(2^{n+2}) を右の u^(2^{n+1}) で潰す）
theorem RedEq_absorb_pow2Sq_right {α : Type} (t u : Term α) :
  ∀ n : Nat,
    RedEq ((t.op (pow2Sq (n+1) u)).op (pow2Sq n u)) (t.op (pow2Sq n u))
  | 0 => by
      -- n=0 は元の DoubleSq（u⁴ を u² で潰す）
      simpa [pow2Sq] using
        (RedEq_absorb_doubleSq_right (α := α) (t := t) (u := u))
  | n+1 => by
      -- u を pow2Sq n u に置換した DoubleSq がそのまま次段
      simpa [pow2Sq] using
        (RedEq_absorb_doubleSq_right (α := α) (t := t) (u := pow2Sq n u))

-- u, u², u⁴, u⁸, ... という塔
def pow2 {α : Type} : Nat → Term α → Term α
  | 0, u => u
  | n+1, u =>
      let v := pow2 n u
      v.op v
--Decor も同じ：スキーマ閉包で派生列を作れる
theorem RedEq_decor_pow2 {α : Type} (t u : Term α) :
  ∀ n : Nat,
    RedEq (((t.op (pow2 n u)).op ((pow2 n u).op ((pow2 n u).op (pow2 n u)))))
         (t.op (pow2 n u))
  | n => by
      -- ただの置換。中身は decor の再利用
      simpa [pow2] using (RedEq_decor_uuu (α := α) (t := t) (u := pow2 n u))
--SqAbsorb の塔（u ↦ pow2 n u の置換閉包）
theorem RedEq_absorb_sq_right_pow2 {α : Type} (t u : Term α) :
  ∀ n : Nat,
    RedEq (α := α)
      ((t.op (pow2 n u)).op ((pow2 n u).op (pow2 n u)))
      (t.op (pow2 n u))
  | n => by
      -- ただの置換：u := pow2 n u
      simpa using
        (RedEq_absorb_sq_right (α := α) (t := t) (u := pow2 n u))
--SqStable の塔（安定性も同じく置換で閉じる）
theorem RedEq_sq_right_stable_pow2 {α : Type} (t u : Term α) :
  ∀ n : Nat,
    RedEq (α := α)
      ((((t.op (pow2 n u)).op ((pow2 n u).op (pow2 n u))).op (pow2 n u)))
      (((t.op (pow2 n u)).op ((pow2 n u).op (pow2 n u))))
  | n => by
      simpa using
        (RedEq_sq_right_stable (α := α) (t := t) (u := pow2 n u))
--C2C1 の塔（z ↦ pow2 n z の置換閉包）
theorem RedEq_C2C1_right_pow2 {α : Type} (x p z : Term α) :
  ∀ n : Nat,
    RedEq (α := α)
      (((x.op (p.op (pow2 n z))).op (pow2 n z)).op (p.op (pow2 n z)))
      ((x.op (p.op (pow2 n z))).op (pow2 n z))
  | n => by
      simpa using
        (RedEq_C2C1_right (α := α) (x := x) (p := p) (z := pow2 n z))


theorem RedEq_jumpDecor2 {α : Type} (t u : Term α) :
  RedEq (α := α) ((t.op u).op (u.op (pow2 2 u))) (t.op u) := by
  let u2 : Term α := u.op u
  let u4 : Term α := u2.op u2
  -- u4 ≈ u2  (SqAbsorb で t=u, u=u)
  have hu4 : RedEq (α := α) u4 u2 := by
    simpa [u2, u4] using
      (RedEq_absorb_sq_right (α := α) (t := u) (u := u))
  -- 合同性で u⋆u4 ≈ u⋆u2
  have huu : RedEq (α := α) (u.op u4) (u.op u2) := by
    simpa [u2, u4] using
      (RedEq_op_right (α := α) (t₁ := u) hu4)
  -- さらに外側の右引数を置換： (t⋆u)⋆(u⋆u4) ≈ (t⋆u)⋆(u⋆u2)
  have h1 :
      RedEq (α := α)
        ((t.op u).op (u.op u4))
        ((t.op u).op (u.op u2)) := by
    exact RedEq_op_right (α := α) (t₁ := (t.op u)) huu
  -- Decor： (t⋆u)⋆(u⋆(u⋆u)) ≈ (t⋆u)
  have h2 :
      RedEq (α := α)
        ((t.op u).op (u.op u2))
        (t.op u) := by
    simpa [u2] using
      (RedEq_decor_uuu (α := α) (t := t) (u := u))
  -- 連結して (t⋆u)⋆(u⋆u4) ≈ (t⋆u)
  have h :
      RedEq (α := α)
        ((t.op u).op (u.op u4))
        (t.op u) :=
    EqvGen.trans (r := @Red α) _ _ _ h1 h2
  -- pow2 2 u = u4 に落としてゴールへ
  simpa [pow2, u2, u4] using h

end WAA
end WeakAbsorption
