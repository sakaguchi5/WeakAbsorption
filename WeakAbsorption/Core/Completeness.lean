import WeakAbsorption.Core.Universal
import WeakAbsorption.Core.Semantics

open WeakAbsorption.Closure

namespace WeakAbsorption
namespace Completeness

variable {α : Type}

/-!
  このファイルは **UniversalWAA（普遍性API）** の上に Completeness を載せる。
  目的：Completeness が Free の内部証明（liftHom_unique 等）を直接参照しない構造にする。
-/

/-- 任意の C12 代数 `S` について、恒等準同型。 -/
private def idHom {A : Type} (S : C12Algebra A) : C12Algebra.Hom S S :=
{ toFun := fun x => x
  map_op := by
    intro x y
    rfl
}

/-- `extend` を `mk` に適用すると `Term.eval` になる（定義展開だけ）。 -/
private theorem extend_mk
  {A : Type} (S : C12Algebra A) (ρ : α → A) (t : Term α) :
  UniversalWAA.extend (S := S) (α := α) ρ (Quot.mk RedEq t : WAA α)
    =
  Term.eval S ρ t := by
  rfl

/--
自由代数 `WAA` における `eval` は、そのまま `quot` の代表元になる。

**重要**：ここでは Term の帰納法を使わず、普遍性（extend/restrict）から導く。
-/
@[simp] theorem eval_free_mk (t : Term α) :
    Term.eval (WAA.c12Alg α) WAA.eta t
      =
    (Quot.mk RedEq t : WAA α) := by
  -- S0 := 自由代数自身の C12 構造
  let S0 : C12Algebra (WAA α) := WAA.c12Alg α
  -- 恒等準同型
  let f : C12Algebra.Hom S0 S0 := idHom S0
  -- restrict f = η
  have hre : UniversalWAA.restrict (S := S0) (α := α) f = WAA.eta := by
    funext a
    rfl
  -- extend η = f （普遍性の「extend ∘ restrict = id」を使う）
  have hext : UniversalWAA.extend (S := S0) (α := α) (WAA.eta) = f := by
    -- extend (restrict f) = f を、restrict f = η で書き換えるだけ
    simpa [hre] using (UniversalWAA.extend_restrict (S := S0) (α := α) f)
  -- あとは mk t に適用して終わり
  calc
    Term.eval S0 WAA.eta t
        =
      UniversalWAA.extend (S := S0) (α := α) (WAA.eta) (Quot.mk RedEq t : WAA α) := by
          -- extend_mk の左右をひっくり返す
          symm
          exact extend_mk (S := S0) (ρ := WAA.eta) t
    _   = f (Quot.mk RedEq t : WAA α) := by
          -- extend η = f
          simp [hext]
    _   = (Quot.mk RedEq t : WAA α) := by
          rfl

/--
（自由代数での `eval` 一致）→ `RedEq`。

この補題に落とすと、「全モデル」仮定を実際には `WAA` 1点にしか使っていないことが
露出する（= 定理の実体が見える）。
-/
theorem RedEq_of_eval_free (t u : Term α)
    (h : Term.eval (WAA.c12Alg α) WAA.eta t =
        Term.eval (WAA.c12Alg α) WAA.eta u) :
    RedEq t u := by
  -- `eval_free_mk` により、自由代数での `eval` の等式はそのまま `Quot.mk` の等式になる。
  have h_quot : (Quot.mk RedEq t : WAA α) = Quot.mk RedEq u := by
    simpa [eval_free_mk] using h
  -- ここが設計上の要点：Quot.eq で "内部の EqvGen" を取り出さない。
  -- `proj_complete`（transport 版 completeness）で直接 RedEq を得る。
  have h_proj : WAA.proj (α := α) t = WAA.proj (α := α) u := by
    simpa [WAA.proj] using h_quot
  exact WAA.proj_complete (α := α) t u h_proj

/--
Completeness:
すべての C12 モデルで `eval` が一致するなら、項は `RedEq` によって同値である。

実体としては「全モデル」ではなく、特に自由代数 `WAA` での一致だけを使う。
（初期性：任意の意味論は自由代数の像として因数分解される。）
-/
theorem RedEq_of_semantic (t u : Term α)
    (h : ∀ (A : Type) (S : C12Algebra A) (ρ : α → A),
        Term.eval S ρ t = Term.eval S ρ u) :
    RedEq t u := by
  -- 「すべてのモデルで一致」なので、とくに自由代数 (WAA) でも一致する。
  exact RedEq_of_eval_free (α := α) t u (h (WAA α) (WAA.c12Alg α) WAA.eta)


/--
Main theorem: Semantic equality and RedEq are equivalent.
(Soundness ↔ Completeness)
-/
theorem RedEq_iff_semantic (t u : Term α) :
    RedEq t u ↔
    ∀ (A : Type) (S : C12Algebra A) (ρ : α → A),
      Term.eval S ρ t = Term.eval S ρ u := by
  constructor
  · -- Soundness
    intro h A S ρ
    exact Semantics.eval_RedEq (S := S) (ρ := ρ) h
  · -- Completeness
    intro h
    exact RedEq_of_semantic (α := α) t u h


end Completeness
end WeakAbsorption
