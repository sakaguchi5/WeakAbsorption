namespace WeakAbsorption
namespace Laws

/-- 有限集合 `Fin n` 上の二項演算（探索用） -/
abbrev BinOp (n : Nat) := Fin n → Fin n → Fin n

/-- Bool で判定する法則（探索用） -/
abbrev LawB (n : Nat) := BinOp n → Bool

/-- Prop で表す法則（証明・定理化用） -/
def HoldsC1P {A : Type} (op : A → A → A) : Prop :=
  ∀ x y, op (op x y) y = op x y

def HoldsC2pP {A : Type} (op : A → A → A) : Prop :=
  ∀ x y z, op (op (op x y) z) (op y z) = op (op x y) z

/-- あなたの混合候補 M2（Prop版） -/
def HoldsM2P {A : Type} (op : A → A → A) : Prop :=
  ∀ x y z, op (op (op x y) z) (op y (op z z)) = op (op x y) z

/-- Bool版 C1（探索用） -/
def holdsC1B {n : Nat} : LawB n := fun op =>
  decide (∀ x y : Fin n, op (op x y) y = op x y)

/-- Bool版 C2'（探索用） -/
def holdsC2pB {n : Nat} : LawB n := fun op =>
  decide (∀ x y z : Fin n, op (op (op x y) z) (op y z) = op (op x y) z)

/-- Bool版 M2（探索用） -/
def holdsM2B {n : Nat} : LawB n := fun op =>
  decide (∀ x y z : Fin n, op (op (op x y) z) (op y (op z z)) = op (op x y) z)

/-- 複合法則（探索用）：すべて true なら true -/
def allB {n : Nat} (laws : List (LawB n)) : LawB n := fun op =>
  (laws.all (fun L => L op))

end Laws
end WeakAbsorption
