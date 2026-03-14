namespace WeakAbsorption.Tooling.WAProbe

/-- `Fin n` の全要素列挙（coreのみ） -/
def finList (n : Nat) : List (Fin n) :=
  match n with
  | 0 => []
  | n + 1 => (finList n).map (fun i => i.castSucc) ++ [Fin.last n]

def listAll {α : Type} (xs : List α) (p : α → Bool) : Bool :=
  xs.foldr (fun x acc => p x && acc) true

def find? {α : Type} (xs : List α) (p : α → Bool) : Option α :=
  let rec go
    | [] => none
    | x :: xs => if p x then some x else go xs
  go xs

def app2 {n : Nat} (op : Fin n → Fin n → Fin n) (f x y : Fin n) : Fin n :=
  op (op f x) y

def app3 {n : Nat} (op : Fin n → Fin n → Fin n) (f a b c : Fin n) : Fin n :=
  op (op (op f a) b) c

/-- K: ((k⋆a)⋆b)=a -/
def isK {n : Nat} (op : Fin n → Fin n → Fin n) (k : Fin n) : Bool :=
  listAll (finList n) (fun a =>
    listAll (finList n) (fun b =>
      decide (app2 op k a b = a)
    )
  )

/-- S: (((s⋆a)⋆b)⋆c) = (a⋆c)⋆(b⋆c) -/
def isS {n : Nat} (op : Fin n → Fin n → Fin n) (s : Fin n) : Bool :=
  listAll (finList n) (fun a =>
    listAll (finList n) (fun b =>
      listAll (finList n) (fun c =>
        decide (app3 op s a b c = op (op a c) (op b c))
      )
    )
  )

/-- Y: (y⋆f) = f⋆(y⋆f) （固定点方程式） -/
def isY {n : Nat} (op : Fin n → Fin n → Fin n) (y : Fin n) : Bool :=
  listAll (finList n) (fun f =>
    let yf := op y f
    decide (yf = op f yf)
  )

def findK? {n : Nat} (op : Fin n → Fin n → Fin n) : Option (Fin n) :=
  find? (finList n) (isK op)

def findS? {n : Nat} (op : Fin n → Fin n → Fin n) : Option (Fin n) :=
  find? (finList n) (isS op)

def findY? {n : Nat} (op : Fin n → Fin n → Fin n) : Option (Fin n) :=
  find? (finList n) (isY op)

def isLeftAbsorbing {n} (op : Fin n → Fin n → Fin n) (a : Fin n) : Bool :=
  listAll (finList n) (fun x =>
    decide (op a x = a)
  )

def isRightAbsorbing {n} (op : Fin n → Fin n → Fin n) (a : Fin n) : Bool :=
  listAll (finList n) (fun x =>
    decide (op x a = a)
  )
def allY {n : Nat} (op : Fin n → Fin n → Fin n) : List (Fin n) :=
  (finList n).filter (fun y => isY op y)

def yImage {n : Nat} (op : Fin n → Fin n → Fin n) (y : Fin n) : List (Fin n) :=
  (finList n).map (fun f => op y f)

def isConstant {α : Type} [DecidableEq α] (xs : List α) : Bool :=
  match xs with
  | [] => true
  | x :: xs => listAll xs (fun z => decide (z = x))

def isConstantYImage {n : Nat} (op : Fin n → Fin n → Fin n) (y : Fin n) : Bool :=
  isConstant (yImage op y)

def fixedPointsOf {n : Nat} (op : Fin n → Fin n → Fin n) (f : Fin n) : List (Fin n) :=
  (finList n).filter (fun a => decide (op f a = a))

def dedup {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldr (fun x acc => if x ∈ acc then acc else x :: acc) []

def imageR {n : Nat} (op : Fin n → Fin n → Fin n) (f : Fin n) : List (Fin n) :=
  dedup ((finList n).map (fun y => op y f))

def subsetList {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  listAll xs (fun x => decide (x ∈ ys))

def sameSet {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  subsetList xs ys && subsetList ys xs

def reportRF {n : Nat} (op : Fin n → Fin n → Fin n) : List (Fin n × List (Fin n) × List (Fin n) × Bool) :=
  (finList n).map (fun f =>
    let im := imageR op f
    let fx := fixedPointsOf op f
    (f, im, fx, sameSet im fx)
  )
def yIsVacuous {n : Nat} (op : Fin n → Fin n → Fin n) : Bool :=
  listAll (finList n) (fun f =>
    listAll (finList n) (fun y =>
      let a := op y f
      decide (op f a = a)
    )
  )

end WeakAbsorption.Tooling.WAProbe
