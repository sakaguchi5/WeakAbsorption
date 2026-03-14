import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.FinRange

namespace WeakAbsorption
namespace ModelSearch

open scoped BigOperators

/-- 右作用 `f : Fin n → Fin n` をベクタで表現（値表） -/
structure IMap (n : Nat) where
  table : Vector (Fin n) n
deriving DecidableEq, Repr

namespace IMap

variable {n : Nat}

def app (f : IMap n) (x : Fin n) : Fin n :=
  f.table.get x

def comp (g f : IMap n) : IMap n :=
  ⟨Vector.ofFn (fun x => g.app (f.app x))⟩

def fixSet (f : IMap n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => f.app x = x)

def image (h : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.image h

def isIdem (f : IMap n) : Bool :=
  decide (∀ x : Fin n, f.app (f.app x) = f.app x)

end IMap

/-- 長さ k の `Fin n` ベクタ全列挙 -/
def allVec (n : Nat) : (k : Nat) → List (Vector (Fin n) k)
  | 0 => [⟨#[], rfl⟩]
  | k+1 =>
      (allVec n k).flatMap (fun v =>
        (List.finRange n).map (fun a => ⟨v.toArray.push a, by simp [v.2]⟩))

/-- `Fin n → Fin n` の全列挙（IMap として） -/
def allMaps (n : Nat) : List (IMap n) :=
  (allVec n n).map (fun v => ⟨v⟩)

/-- 冪等写像のみ -/
def idemMaps (n : Nat) : List (IMap n) :=
  (allMaps n).filter (fun f => f.isIdem)

/-- C2' を写像制約で書いたもの：
    w = fz(y) として Im(fz ∘ fy) ⊆ Fix(fw) -/
def C2pConstraint {n : Nat} (fy fz fw : IMap n) (y : Fin n) : Prop :=
  let _w : Fin n := fz.app y
  let img : Finset (Fin n) := IMap.image (fun x => fz.app (fy.app x))
  img ⊆ fw.fixSet

/-- 状態：各列 y の右作用 f_y を「冪等写像の候補」から選ぶ。
    assigned[y] = some idx なら、idem[idx] が f_y と確定。 -/
structure State (n : Nat) where
  assigned : Array (Option Nat)      -- size = n
  cands    : Array (List Nat)        -- size = n
deriving Repr

namespace State
variable {n : Nat}

def init (idem : Array (IMap n)) : State n :=
  let idxs : List Nat := List.range idem.size
  { assigned := Array.replicate n none
  , cands := Array.replicate n idxs }

def isAssigned (st : State n) (y : Fin n) : Bool :=
  st.assigned[y.1]!.isSome

def getMap? (idem : Array (IMap n)) (st : State n) (y : Fin n) : Option (IMap n) := do
  let i ← st.assigned[y.1]!
  idem[i]?

def setAssign (st : State n) (y : Fin n) (i : Nat) : State n :=
  { assigned := st.assigned.set! y.1 (some i)
  , cands := st.cands.set! y.1 [i] }

def updateCands (st : State n) (y : Fin n) (new : List Nat) : State n :=
  { st with cands := st.cands.set! y.1 new }

def candsLen (st : State n) (y : Fin n) : Nat :=
  (st.cands[y.1]!).length

end State

/-- 伝播：確定済み fy,fz から w=fz(y) を計算し、
    fw が未確定なら候補を削り、確定なら制約チェックで矛盾なら失敗。 -/
def propagate {n : Nat} (idem : Array (IMap n)) (st : State n) : Option (State n) := Id.run do
  let ys : List (Fin n) := List.finRange n
  let zs : List (Fin n) := List.finRange n
  let mut st' := st
  for y in ys do
    for z in zs do
      match State.getMap? idem st' y, State.getMap? idem st' z with
      | some fy, some fz =>
          let w : Fin n := fz.app y
          let img : Finset (Fin n) := IMap.image (fun x => fz.app (fy.app x))
          if State.isAssigned st' w then
            -- fw が確定：制約が破れてたら失敗
            match State.getMap? idem st' w with
            | some fw =>
                if !decide (img ⊆ fw.fixSet) then
                  return none
            | none => return none
          else
            -- fw 未確定：候補を削る
            let old := st'.cands[w.1]!
            let new := old.filter (fun i =>
              match idem[i]? with
              | some fw => decide (img ⊆ fw.fixSet)
              | none => false)
            if new.isEmpty then
              return none
            st' := st'.updateCands w new
      | _, _ => () -- pure () の代わりに () で何もしないことを明示
  return some st'

/-- 未確定の列で、候補が最小のものを選ぶ（MRV） -/
def pickVar {n : Nat} (st : State n) : Option (Fin n) :=
  -- do ブロックが不要な単純な純粋関数として記述
  let vars := (List.finRange n).filter (fun y => !(State.isAssigned st y))
  match vars with
  | [] => none
  | v :: vs =>
      let best := vs.foldl
        (fun b y => if State.candsLen st y < State.candsLen st b then y else b) v
      some best

/-- C1+C2' モデルを1つ見つける（右作用を冪等写像から構成） -/
partial def searchModel {n : Nat} (idem : Array (IMap n)) (st : State n)
  : Option (State n) := Id.run do
  match propagate idem st with
  | none => return none
  | some st' =>
      match pickVar st' with
      | none => return some st'
      | some y =>
          let opts := st'.cands[y.1]!
          for i in opts do
            match searchModel idem (st'.setAssign y i) with
            | some sol => return some sol
            | none => ()
          return none

/-- 完成状態から op を取り出す -/
def opOf {n : Nat} (idem : Array (IMap n)) (sol : State n) : Fin n → Fin n → Fin n :=
  fun x y =>
    match sol.assigned[y.1]! with
    | some i =>
        match idem[i]? with
        | some f => f.app x
        | none => x
    | none => x   -- 未完成は使わない想定（保険）



/-- n でモデルが見つかるかを試す -/
def findOneModel (n : Nat) : Option (Fin n → Fin n → Fin n) :=
  let idem := (idemMaps n).toArray
  match searchModel idem (State.init idem) with
  | some sol => some (opOf idem sol)
  | none => none

/-- 混合候補 M2:
    (((x⋆y)⋆z)⋆(y⋆(z⋆z))) = ((x⋆y)⋆z)
-/
def holdsM2 {n : Nat} (op : Fin n → Fin n → Fin n) : Bool :=
  decide (∀ x y z : Fin n,
    op (op (op x y) z) (op y (op z z)) = op (op x y) z)

def isCounterexampleM2 {n : Nat} (idem : Array (IMap n)) (sol : State n) : Bool :=
  let op := opOf idem sol
  !(holdsM2 op)

/-- C1+C2' を満たし、かつ M2 を壊すモデルを1つ探す -/
partial def searchCounterexampleM2 {n : Nat} (idem : Array (IMap n)) (st : State n)
  : Option (State n) := Id.run do
  match propagate idem st with
  | none => return none
  | some st' =>
      match pickVar st' with
      | none =>
          if isCounterexampleM2 idem st' then
            return some st'
          else
            return none
      | some y =>
          let opts := st'.cands[y.1]!
          for i in opts do
            match searchCounterexampleM2 idem (st'.setAssign y i) with
            | some sol => return some sol
            | none => ()
          return none

def findCounterexampleM2 (n : Nat) : Option (Fin n → Fin n → Fin n) :=
  let idem := (idemMaps n).toArray
  match searchCounterexampleM2 idem (State.init idem) with
  | some sol => some (opOf idem sol)
  | none => none

def opTable {n : Nat} (op : Fin n → Fin n → Fin n) : List (List Nat) :=
  (List.finRange n).map (fun x =>
    (List.finRange n).map (fun y => (op x y).1))




end ModelSearch
end WeakAbsorption


-- 1. 冪等写像の数を確認 -/
--#eval (WeakAbsorption.ModelSearch.idemMaps 3).length --
--#eval (WeakAbsorption.ModelSearch.idemMaps 4).length -- 41
--#eval (WeakAbsorption.ModelSearch.idemMaps 5).length -- 196

-- 2. モデルの探索実行 (n=3) -/
--#eval (WeakAbsorption.ModelSearch.findOneModel 3).isSome

-- 3. M2 を満たさない反例の探索 -/
--#eval (WeakAbsorption.ModelSearch.findCounterexampleM2 3).isSome

--#eval match WeakAbsorption.ModelSearch.findCounterexampleM2 4 with
  --| some op => WeakAbsorption.ModelSearch.opTable op
  --| none => []
