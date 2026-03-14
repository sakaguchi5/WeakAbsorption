import WeakAbsorption.Core.Quotient
import WeakAbsorption.Core.Termination
/-!
LAYER: CANONICAL (noncomputable representatives, NFQuot, WAA ≃ NFQuot)
MAY import: Quotient + Termination (+ minimal Mathlib.Tactic)
MUST NOT import: Semantics / Free / Universal / Completeness (keep metatheory clean)
Note: contains Classical.choice and depends on exists_normal_form (existence, not an algorithm).
-/
------------------------------------------------

open WeakAbsorption.Closure

namespace WeakAbsorption

namespace WAA

variable {α : Type}

noncomputable section
/-- 任意の同値類 `x : WAA α` には、必ずある代表 `t : Term α` が存在して `proj t = x` となる。 -/
theorem exists_rep (x : WAA α) :
     ∃ t : Term α, proj (α := α) t = x := by
  -- 商型の帰納法（Quot.inductionOn）により、任意の x はある t の射影であることを示す
  refine Quot.inductionOn x ?_
  intro t
  exact ⟨t, rfl⟩
/-- （N1の最小形）同値類から代表元を1つ選ぶ。非計算的（Classical.choice）。 -/
noncomputable def rep (x : WAA α) : Term α :=
  Classical.choose (exists_rep (α := α) x)
/-- `proj ∘ rep = id`（代表を選んでから射影すると元に戻る）。 -/
@[simp] theorem proj_rep (x : WAA α) :
   proj (α := α) (rep (α := α) x) = x :=
  Classical.choose_spec (exists_rep (α := α) x)

/-- `rep (proj t)` は `t` と RedEq 同値（同値類の中の別代表を選んだだけ）。 -/
theorem rep_proj_RedEq (t : Term α) :
    RedEq (rep (α := α) (proj (α := α) t)) t := by
  have h : proj (α := α) (rep (α := α) (proj (α := α) t))
          = proj (α := α) t := by
    simp
  exact (proj_eq_iff (α := α)
          (t := rep (α := α) (proj (α := α) t))
          (u := t)).1 h
end

noncomputable section
/-- RedStar で到達できるなら RedEq（= EqvGen Red）でも同値。 -/
theorem RedEq_of_RedStar {t u : Term α} (h : RedStar t u) : RedEq t u := by
  induction h
  case refl =>
    -- 自身の同値
    exact EqvGen.refl _
  case tail mid u h_t_to_mid h_step_to_u ih =>
    -- mid : 途中経過の項
    -- u   : 最終的な項
    -- h_t_to_mid : RedStar t mid (反射推移閉包)
    -- h_step_to_u : Red mid u (最後の一歩の簡約)
    -- ih  : RedEq t mid (帰納法の仮定：すでに同値であることが証明済み)

    -- 最後の一歩 (Red mid u) を同値関係 (RedEq mid u) に変換
    let h_eq_step : RedEq mid u := EqvGen.rel _ _ h_step_to_u
    -- t ≃ mid と mid ≃ u をつないで t ≃ u を導く
    exact EqvGen.trans _ _ _ ih h_eq_step
/-- 矢印版 -/
private theorem RedEq_of_RedStar' {t u : Term α} :
  RedStar (α := α) t u → RedEq t u := by
  intro h; exact RedEq_of_RedStar (α := α) h
/-- 任意の同値類 `x` には、Normal な代表が存在する。 -/
theorem exists_repNF (x : WAA α) :
    ∃ t : Term α, Normal t ∧ proj (α := α) t = x := by
  classical
  -- 1) 代表を1つ取る
  let t0 : Term α := rep (α := α) x
  -- 2) ここで “型を固定して” exists_normal_form を呼ぶ（超重要）
  have hnf :
      ∃ u : Term α, RedStar (α := α) t0 u ∧ Normal u :=
    exists_normal_form (α := α) t0
    -- もし名前空間が違うならここだけ直す（例: Termination.exists_normal_form など）
  rcases hnf with ⟨u, hstar, hnorm⟩
  refine ⟨u, hnorm, ?_⟩
  -- 3) RedStar から RedEq へ
  have hre : RedEq t0 u := RedEq_of_RedStar (α := α) (t := t0) (u := u) hstar
  -- 4) proj u = x を示す：proj_eq_iff を ↔ として使う
  have hu0 : proj (α := α) u = proj (α := α) t0 :=
    (proj_eq_iff (α := α) (t := u) (u := t0)).2 hre.symm
  calc
    proj (α := α) u = proj (α := α) t0 := hu0
    _ = x := by
      simp [t0, proj_rep]

/-- Normal な代表を1つ選ぶ（noncomputable）。 -/
noncomputable def repNF (x : WAA α) : Term α :=
  Classical.choose (exists_repNF (α := α) x)

@[simp] theorem repNF_normal (x : WAA α) : Normal (repNF (α := α) x) :=
  (Classical.choose_spec (exists_repNF (α := α) x)).1

@[simp] theorem proj_repNF (x : WAA α) :
  proj (α := α) (repNF (α := α) x) = x :=
  (Classical.choose_spec (exists_repNF (α := α) x)).2

/-- 元の項 `t` に対し、`repNF (proj t)` は `t` と RedEq 同値で、しかも Normal。 -/
theorem repNF_proj_RedEq (t : Term α) :
  RedEq (repNF (α := α) (proj (α := α) t)) t := by
  have : proj (α := α) (repNF (α := α) (proj (α := α) t)) = proj (α := α) t := by
    simp [proj_repNF]
  exact (proj_eq_iff (α := α)
          (t := repNF (α := α) (proj (α := α) t))
          (u := t)).1 this

/-- Normal な項の部分型（正規形の型） -/
def NormalForm (α : Type) := { t : Term α // Normal t }

/-- NormalForm 上の同値関係（値が RedEq で同値） -/
def NFRel {α : Type} (x y : NormalForm α) : Prop :=
  RedEq x.1 y.1
/-- NormalForm 上の「平方吸収」1ステップ（文脈込み） -/
def NFSqStepCtx {α : Type} (x y : NormalForm α) : Prop :=
  ∃ (C : Ctx α) (t u : Term α),
    x.1 = Ctx.plug C (((t.op u).op (u.op u))) ∧
    y.1 = Ctx.plug C (t.op u)

/-- NormalForm を RedEq で割った商 -/
abbrev NFQuot (α : Type) := Quot (@NFRel α)

def toNF (x : WAA α) : NormalForm α :=
  ⟨repNF (α := α) x, repNF_normal (α := α) x⟩

def fromNF (x : NormalForm α) : WAA α :=
  proj (α := α) x.1

/-- WAA → NFQuot -/
def toNFQuot (x : WAA α) : NFQuot α :=
  Quot.mk _ (toNF (α := α) x)

/-- NFQuot → WAA -/
def fromNFQuot : NFQuot α → WAA α :=
  Quot.lift
    (fun nf : NormalForm α => proj (α := α) nf.1)
    (by
      intro a b hab
      -- hab : RedEq a.1 b.1 から proj a.1 = proj b.1
      exact (proj_eq_iff (α := α) (t := a.1) (u := b.1)).2 hab)

@[simp] theorem fromNFQuot_toNFQuot (x : WAA α) :
  fromNFQuot (α := α) (toNFQuot (α := α) x) = x := by
  -- proj (repNF x) = x
  simp [toNFQuot, fromNFQuot, toNF, proj_repNF]

theorem toNFQuot_fromNFQuot (q : NFQuot α) :
  toNFQuot (α := α) (fromNFQuot (α := α) q) = q := by
  refine Quot.inductionOn q ?_
  intro nf
  -- 代表 nf について示せばよい
  apply Quot.sound
  -- 目標: NFRel (toNF (proj nf.1)) nf
  --      つまり RedEq (repNF (proj t)) t
  cases nf with
  | mk t hnorm =>
    simpa [NFRel, toNF, toNFQuot, fromNFQuot] using
      (repNF_proj_RedEq (α := α) (t := t))
/-Equivがcoreにないのでコメントアウト
/-- これが「正しい」同型 -/
def nfQuotEquiv : WAA α ≃ NFQuot α :=
{ toFun := toNFQuot (α := α)
  invFun := fromNFQuot (α := α)
  left_inv := fromNFQuot_toNFQuot (α := α)
  right_inv := toNFQuot_fromNFQuot (α := α) }
-/
end

noncomputable def chooseNF {α} (t : Term α) : Term α :=
  WAA.repNF (α := α) (WAA.proj (α := α) t)

theorem chooseNF_normal {α} (t : Term α) :
  Normal (α := α) (chooseNF (α := α) t) := by
  simp [chooseNF]

theorem chooseNF_proj {α} (t : Term α) :
  WAA.proj (α := α) (chooseNF (α := α) t) = WAA.proj (α := α) t := by
  -- proj (repNF x) = x を使うだけ
  simp [chooseNF,WAA.proj_repNF (α := α) (x := WAA.proj (α := α) t)]

theorem RedEq_iff_chooseNF_eq {α} (t u : Term α) :
  RedEq t u ↔ chooseNF (α := α) t = chooseNF (α := α) u := by
  constructor
  · intro h
    -- RedEq t u → proj t = proj u → repNF(proj t)=repNF(proj u)
    have : WAA.proj (α := α) t = WAA.proj (α := α) u :=
      (WAA.proj_eq_iff (α := α) (t := t) (u := u)).2 h
    simp [chooseNF, this]
  · intro h
    -- 等号 → proj が等しい → RedEq
    have : WAA.proj (α := α) (chooseNF (α := α) t)
          = WAA.proj (α := α) (chooseNF (α := α) u) := by
      simp [h]
    -- chooseNF_proj で proj chooseNF = proj
    have : WAA.proj (α := α) t = WAA.proj (α := α) u := by
      simpa [chooseNF_proj (α := α) t, chooseNF_proj (α := α) u] using this
    exact (WAA.proj_eq_iff (α := α) (t := t) (u := u)).1 this

end WAA
end WeakAbsorption
