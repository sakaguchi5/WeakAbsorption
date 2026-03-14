namespace WeakAbsorption.Closure
universe u

/-
==================================================
EqvGen : mathlib Relation.EqvGen 完全互換版
==================================================
-/

/-- 等値生成 closure（mathlib Relation.EqvGen 完全互換） -/
inductive EqvGen {α : Type u} (r : α → α → Prop) :
  α → α → Prop
where
| rel (a b : α) :
    r a b →
    EqvGen r a b
| refl (a : α) :
    EqvGen r a a
| symm (a b : α) :
    EqvGen r a b →
    EqvGen r b a
| trans (a b c : α) :
    EqvGen r a b →
    EqvGen r b c →
    EqvGen r a c


namespace EqvGen

@[simp]
theorem rel'
  {α} {r : α → α → Prop} {a b : α}
  (h : r a b) :
  EqvGen r a b :=
rel a b h

@[simp]
theorem refl'
  {α} {r : α → α → Prop} (a : α) :
  EqvGen r a a :=
refl a

@[simp]
theorem symm'
  {α} {r : α → α → Prop}
  {a b : α}
  (h : EqvGen r a b) :
  EqvGen r b a :=
symm a b h

@[simp]
theorem trans'
  {α} {r : α → α → Prop}
  {a b c : α}
  (h₁ : EqvGen r a b)
  (h₂ : EqvGen r b c) :
  EqvGen r a c :=
trans a b c h₁ h₂


/-
Bridge（任意）
Quot.eq を使う場合に必要
完全独立したら削除可能
-/
/-
theorem ofRelation
  {α} {r : α → α → Prop} {a b : α} :
  Relation.EqvGen r a b →
  EqvGen r a b :=
by
  intro h
  induction h with
  | rel x y h =>
      exact rel x y h
  | refl x =>
      exact refl x
  | symm x y h ih =>
      exact symm x y ih
  | trans x y z h₁ h₂ ih₁ ih₂ =>
      exact trans x y z ih₁ ih₂


theorem toRelation
  {α} {r : α → α → Prop} {a b : α} :
  EqvGen r a b →
  Relation.EqvGen r a b :=
by
  intro h
  induction h with
  | rel x y h =>
      exact Relation.EqvGen.rel x y h
  | refl x =>
      exact Relation.EqvGen.refl x
  | symm x y h ih =>
      exact Relation.EqvGen.symm x y ih
  | trans x y z h₁ h₂ ih₁ ih₂ =>
      exact Relation.EqvGen.trans x y z ih₁ ih₂
-/
end EqvGen


/-
==================================================
ReflTransGen : mathlib Relation.ReflTransGen 完全互換版
==================================================
-/

/-- 反射推移 closure（mathlib Relation.ReflTransGen 完全互換） -/
inductive ReflTransGen {α : Type u} (r : α → α → Prop) : α → α → Prop where
| refl {a : α} : ReflTransGen r a a
| tail {a b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c


namespace ReflTransGen

@[simp]
theorem refl'
  {α} {r : α → α → Prop} (a : α) :
  ReflTransGen r a a :=
refl

/-- mathlib互換 single -/
theorem single
  {α} {r : α → α → Prop}
  {a b : α}
  (h : r a b) :
  ReflTransGen r a b :=
tail refl h

/-- パスの左側に1ステップ追加する：`a → b` と `b →* c` から `a →* c` を得る -/
theorem head {α : Type} {r : α → α → Prop} {a b c : α}
    (h_ab : r a b) (h_bc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction h_bc with
  | refl =>
      -- b = c の場合。 a → b なので single で OK
      exact single h_ab
  | tail _ h_tc ih =>
      -- t → c (h_tc) がある状態
      -- ih は帰納法の仮定（a → ... → t）
      -- un-appliedな前提は使わないため `_` で省略
      exact tail ih h_tc

/-- 推移律の証明例 -/
theorem trans {α : Type} {r : α → α → Prop} {a b c : α}
    (h1 : ReflTransGen r a b) (h2 : ReflTransGen r b c) :
    ReflTransGen r a c := by
  induction h2 with
  | refl =>
      exact h1
  | tail _ hbc ih =>
      exact tail ih hbc


end ReflTransGen


end WeakAbsorption.Closure
