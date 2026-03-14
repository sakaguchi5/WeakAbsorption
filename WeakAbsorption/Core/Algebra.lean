namespace WeakAbsorption
structure C12Algebra (A : Type) where
  op : A → A → A
  C1 : ∀ x y, op (op x y) y = op x y
  C2p : ∀ x y z,
    op (op (op x y) z) (op y z) = op (op x y) z

namespace C12Algebra

structure Hom {A B : Type} (S : C12Algebra A) (T : C12Algebra B) where
  toFun : A → B
  map_op : ∀ x y, toFun (S.op x y) = T.op (toFun x) (toFun y)

instance {A B} {S : C12Algebra A} {T : C12Algebra B} :
    CoeFun (Hom S T) (fun _ => A → B) :=
  ⟨Hom.toFun⟩

@[ext] theorem Hom.ext {A B} {S : C12Algebra A} {T : C12Algebra B}
  (f g : Hom S T) (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk ffun fmap =>
    cases g with
    | mk gfun gmap =>
      have : ffun = gfun := funext h
      cases this
      have : fmap = gmap := Subsingleton.elim _ _
      cases this
      rfl

def Hom.id {A : Type} (S : C12Algebra A) : Hom S S :=
{ toFun := fun x => x
  map_op := by
    intro x y
    rfl
}

def Hom.comp {A B C : Type}
  {S : C12Algebra A} {T : C12Algebra B} {U : C12Algebra C}
  (g : Hom T U) (f : Hom S T) : Hom S U :=
{ toFun := fun x => g (f x)
  map_op := by
    intro x y
    -- g (f (S.op x y)) = U.op (g (f x)) (g (f y))
    calc
      g (f (S.op x y)) = g (T.op (f x) (f y)) := by
        -- f.map_op を g に食わせる
        simpa using congrArg g (f.map_op x y)
      _ = U.op (g (f x)) (g (f y)) := by
        simpa using g.map_op (f x) (f y)
}

@[simp] theorem Hom.id_apply {A : Type} (S : C12Algebra A) (x : A) :
  Hom.id S x = x := rfl

@[simp] theorem Hom.comp_apply {A B C : Type}
  {S : C12Algebra A} {T : C12Algebra B} {U : C12Algebra C}
  (g : Hom T U) (f : Hom S T) (x : A) :
  Hom.comp g f x = g (f x) := rfl



end C12Algebra

end WeakAbsorption
