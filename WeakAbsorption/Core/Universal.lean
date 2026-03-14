import WeakAbsorption.Core.Free
namespace WeakAbsorption.UniversalWAA

variable {α A : Type} (S : C12Algebra A)

-- 生成元への制限（Hom → (α → A)）
def restrict (f : C12Algebra.Hom (WAA.c12Alg α) S) : α → A :=
  fun a => f (WAA.eta a)

-- 生成元写像の拡張（(α → A) → Hom）
def extend (ρ : α → A) : C12Algebra.Hom (WAA.c12Alg α) S :=
  FreeWAA.liftHom (S := S) (ρ := ρ)

-- extend ∘ restrict = id
theorem extend_restrict (f : C12Algebra.Hom (WAA.c12Alg α) S) :
  extend (S := S) (α := α) (restrict (S := S) (α := α) f) = f := by
  -- ρ := restrict f として、Free の一意性で潰す
  -- （左右を逆にしたいなら `symm` を外す）
  symm
  refine FreeWAA.liftHom_unique (S := S)
    (ρ := restrict (S := S) (α := α) f) f ?_
  intro a
  rfl

-- restrict ∘ extend = id
theorem restrict_extend (ρ : α → A) :
  restrict (S := S) (α := α) (extend (S := S) (α := α) ρ) = ρ := by
  funext a
  -- η-law
  simp [restrict, extend]

/-Equiv
圏論的レベル求められるまでは一度コメントアウト
-- 普遍性を Equiv で提供
def homEquiv : (C12Algebra.Hom (WAA.c12Alg α) S) ≃ (α → A) :=
{ toFun := restrict (S := S) (α := α)
  invFun := extend (S := S) (α := α)
  left_inv := by
    intro f
    -- extend_restrict は = f を返すのでそのまま
    simpa using (extend_restrict (S := S) (α := α) f)
  right_inv := by
    intro ρ
    simpa using (restrict_extend (S := S) (α := α) ρ)
}
-/
-- Free functor（既存構成の別名）
def Free (α : Type) :=
  WAA.c12Alg α

-- Forget functor（既存構成の別名）
def Forget {A : Type} (_S : C12Algebra A) :=
  A

-- unit（η）
def unit (α : Type) : α → Forget (Free α) :=
  WAA.eta

-- counit（ε）
def counit {A : Type} (S : C12Algebra A) :
  C12Algebra.Hom (Free (Forget S)) S :=
  extend (S := S) (α := Forget S) (id : A → A)
-- ==========================================
-- Triangle Identities (三角等式)
-- ==========================================

-- 右三角等式（Forget側）： U(ε_S) ∘ η_U(S) = id_U(S)
theorem right_triangle {A : Type} (S : C12Algebra A) (a : Forget S) :
  counit S (unit (Forget S) a) = a := by
  -- counit は extend id であり、unit は WAA.eta
  -- つまり左辺は extend id (WAA.eta a) となる
  -- restrict の定義 (f (eta a)) により、これは restrict (extend id) a に等しい
  change restrict (S := S) (α := Forget S) (extend (S := S) (α := Forget S) (id : A → A)) a = id a
  -- restrict_extend (ρ = id) を適用して解決
  rw [restrict_extend]
-- Free関手の射に対する作用（map）
def mapFree {α β : Type} (f : α → β) : C12Algebra.Hom (Free α) (Free β) :=
  extend (S := Free β) (α := α) (unit β ∘ f)

theorem mapFree_id {α : Type} :
  mapFree (α := α) (β := α) (fun a => a) = C12Algebra.Hom.id (Free α) := by
  have h_left :
      mapFree (α := α) (β := α) (fun a => a)
        = FreeWAA.liftHom (S := Free α) (ρ := WAA.eta) := by
    apply FreeWAA.liftHom_unique
    intro a
    simp [mapFree, extend, unit]
  have h_right :
      C12Algebra.Hom.id (Free α)
        = FreeWAA.liftHom (S := Free α) (ρ := WAA.eta) := by
    apply FreeWAA.liftHom_unique
    intro a
    rfl
  rw [h_left, h_right]

theorem mapFree_comp {α β γ : Type} (f : α → β) (g : β → γ) :
  mapFree (g ∘ f) = C12Algebra.Hom.comp (mapFree g) (mapFree f) := by
  -- 左辺が liftHom としてどう振る舞うかを示す
  have h_left :
      mapFree (g ∘ f)
        = FreeWAA.liftHom (S := Free γ) (ρ := fun a => WAA.eta (g (f a))) := by
    apply FreeWAA.liftHom_unique
    intro a
    -- mapFree の定義を展開すると eta (g (f a)) になる
    simp [mapFree, extend, unit]
  -- 右辺が liftHom としてどう振る舞うかを示す
  have h_right :
      C12Algebra.Hom.comp (mapFree g) (mapFree f)
        = FreeWAA.liftHom (S := Free γ) (ρ := fun a => WAA.eta (g (f a))) := by
    apply FreeWAA.liftHom_unique
    intro a
    -- comp された Hom に eta a を適用していくと、
    -- mapFree f によって eta (f a) になり、
    -- さらに mapFree g によって eta (g (f a)) になる
    simp [mapFree, extend, unit]
  -- 両辺が同じ liftHom に等しいので、互いに等しい
  rw [h_left, h_right]


-- 左三角等式（Free側）： ε_F(α) ∘ F(η_α) = id_F(α)
theorem left_triangle {α : Type} (x : WAA α) :
  counit (Free α) (mapFree (unit α) x) = x := by
  -- 合成された準同型が恒等写像に等しいこと（Homとしての等式）を示す
  have H : C12Algebra.Hom.comp (counit (Free α)) (mapFree (unit α))
    = C12Algebra.Hom.id (Free α) := by
    -- 双方のHomが生成元 `WAA.eta` 上で一致することを示し、
    -- liftHom_unique (普遍性による一意性) を経由して一致させる

    -- 左辺が liftHom (Free α) WAA.eta に等しいこと
    have h_left : C12Algebra.Hom.comp (counit (Free α)) (mapFree (unit α))
      = FreeWAA.liftHom (Free α) WAA.eta := by
      apply FreeWAA.liftHom_unique
      intro a
      -- counit (mapFree (eta a)) を計算する
      -- mapFree f (eta a) = f a、counit (eta y) = y となることを simp で解決
      simp [counit, mapFree, extend, unit]
    -- 右辺(id)が liftHom (Free α) WAA.eta に等しいこと
    have h_right : C12Algebra.Hom.id (Free α) = FreeWAA.liftHom (Free α) WAA.eta := by
      apply FreeWAA.liftHom_unique
      intro a
      rfl
    -- 2つの等式を繋げる
    rw [h_left, h_right]
  -- Homとしての等式 H の両辺を要素 x に適用する
  have Hx : C12Algebra.Hom.comp (counit (Free α)) (mapFree (unit α)) x
    = C12Algebra.Hom.id (Free α) x := by
    rw [H]
  -- Hom.comp と Hom.id の適用は定義通りなので exact で通る
  exact Hx

/-Equiv
圏論的レベル求められるまでは一度コメントアウト
/-- The Free ⊣ Forget adjunction as an equivalence. -/
def adjunction {α A : Type} (S : C12Algebra A) :
  C12Algebra.Hom (Free α) S ≃ (α → Forget S) :=
{ toFun :=
    restrict (S := S) (α := α)
  invFun :=
    extend (S := S) (α := α)
  left_inv := by
    intro f
    exact extend_restrict (S := S) (α := α) f

  right_inv := by
    intro ρ
    exact restrict_extend (S := S) (α := α) ρ
}
-/
theorem counit_naturality
  {A B : Type}
  {S : C12Algebra A}
  {T : C12Algebra B}
  (k : C12Algebra.Hom S T) :
  C12Algebra.Hom.comp k (counit (S := S))
  =
  C12Algebra.Hom.comp
    (counit (S := T))
    (mapFree (fun a : A => k a)) := by
  -- 左辺を liftHom の形に落とす
  have h_left :
      C12Algebra.Hom.comp k (counit (S := S))
      =
      FreeWAA.liftHom (S := T) (ρ := fun a : A => k a) := by
    apply FreeWAA.liftHom_unique
    intro a
    simp [counit, extend, C12Algebra.Hom.comp]
  -- 右辺も liftHom の形に落とす
  have h_right :
      C12Algebra.Hom.comp
        (counit (S := T))
        (mapFree (fun a : A => k a))
      =
      FreeWAA.liftHom (S := T) (ρ := fun a : A => k a) := by
    apply FreeWAA.liftHom_unique
    intro a
    simp [counit, mapFree, extend, unit, C12Algebra.Hom.comp]
  rw [h_left, h_right]

end WeakAbsorption.UniversalWAA
