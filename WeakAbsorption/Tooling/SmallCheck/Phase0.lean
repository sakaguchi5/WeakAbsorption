import WeakAbsorption.Core.Syntax
import WeakAbsorption.Spec.Rule
import WeakAbsorption.Core.Rewrite

namespace WeakAbsorption
namespace SmallCheck

open WeakAbsorption.Spec

/-
Phase0 SmallCheck:
- vars = 1
- size bound K
- enumerate terms of size ≤ K
- build two undirected graphs (within bound):
    G_red : edges from one-step Red (C1/C2' anywhere)
    G_gen : edges from one-step generator rules (SqAbsorb/SqStable/C2C1/Decor/DoubleSq anywhere)
- find a pair of NORMAL terms u≠v such that:
    connected in G_red  but NOT connected in G_gen
-/

abbrev V := Fin 1

/-- size of Term (local, independent of Core.Measure) -/
def tsize {α : Type} : Term α → Nat
  | .var _   => 1
  | .op t u  => tsize t + tsize u + 1

/-- [0, 1, ..., n-1] を生成する (core-only) -/
def range : Nat → List Nat
  | 0 => []
  | n + 1 => (range n).map (fun i => i) ++ [n]

def lbind {α β : Type} : List α → (α → List β) → List β
  | [], _ => []
  | x :: xs, f => f x ++ lbind xs f

/-- erase duplicates (core-only) -/
def eraseDups {α : Type} [DecidableEq α] : List α → List α
  | []      => []
  | x :: xs =>
      if x ∈ xs then eraseDups xs else x :: eraseDups xs


/-- all terms of EXACT size m over vars=1 -/
def termsExact : Nat → List (Term V)
  | 0 => []
  | 1 => [Term.var 0]
  | m+2 =>
      -- range m を attach することで、各要素 k に対して「k < m」という証拠 h が付随します
      (List.range m).attach.flatMap (fun ⟨k, hk⟩ =>
        let i := k + 1              -- i ∈ {1..m}
        let j := (m + 1) - i        -- j ∈ {1..m}
        -- ここで i < m+2 や j < m+2 を示すのに hk : k < m が使えます
        (termsExact i).flatMap (fun t =>
          (termsExact j).map (fun u => Term.op t u)))
termination_by n => n
decreasing_by
  -- i < m + 2 の証明
  · simp_all
    omega
  -- j < m + 2 の証明
  · simp_all
    omega

/-- all terms of size ≤ K -/
def termsUpTo : Nat → List (Term V)
  | 0 => []
  | k+1 => (termsUpTo k) ++ (termsExact (k+1))

/-- root C1/C2' reductions (no context) -/
def redRoot {α : Type} [DecidableEq (Term α)] : Term α → List (Term α)
  -- C2'
  | .op (.op (.op x y1) z1) (.op y2 z2) =>
      if y1 = y2 ∧ z1 = z2 then
        [.op (.op x y1) z1]
      else
        []
  -- C1
  | .op (.op x y1) y2 =>
      if y1 = y2 then
        [.op x y1]
      else
        []
  | _ => []

/-- all one-step Red successors (context-closed), computed structurally -/
def redNext {α : Type} [DecidableEq (Term α)] : Term α → List (Term α)
  | Term.var _ => []
  | Term.op t u =>
      eraseDups (
        redRoot (Term.op t u)
        ++ (redNext t).map (fun t' => Term.op t' u)
        ++ (redNext u).map (fun u' => Term.op t u')
      )

/-- NORMAL (computable proxy): no Red one-step anywhere -/
def isNormal {α : Type} [DecidableEq (Term α)] (t : Term α) : Bool :=
  (redNext t).isEmpty

/-
Generator rules at root (no context).
These are exactly your 5 schemata, but implemented as syntactic patterns.
-/

/-- generator root reductions for one RuleId -/
def genRoot {α : Type} [DecidableEq (Term α)] : RuleId → Term α → List (Term α)
  | RuleId.SqAbsorb, Term.op (Term.op t u) (Term.op u1 u2) =>
      if (u1 = u) ∧ (u2 = u) then [Term.op t u] else []
  | RuleId.SqAbsorb, _ => []

  | RuleId.SqStable, Term.op (Term.op (Term.op t u) (Term.op u1 u2)) u3 =>
      if (u1 = u) ∧ (u2 = u) ∧ (u3 = u) then [Term.op (Term.op t u) (Term.op u u)] else []
  | RuleId.SqStable, _ => []

  | RuleId.C2C1, Term.op (Term.op (Term.op x (Term.op p z)) z1) (Term.op p1 z2) =>
      if (z1 = z) ∧ (p1 = p) ∧ (z2 = z) then
        [Term.op (Term.op x (Term.op p z)) z]
      else []
  | RuleId.C2C1, _ => []

  | RuleId.Decor, Term.op (Term.op t u) (Term.op u1 (Term.op u2 u3)) =>
      if (u1 = u) ∧ (u2 = u) ∧ (u3 = u) then [Term.op t u] else []
  | RuleId.Decor, _ => []

  | RuleId.DoubleSq, Term.op (Term.op t (Term.op (Term.op u1 u2) (Term.op u3 u4))) (Term.op u5 u6) =>
      -- uu := u⋆u, u4 := uu⋆uu, lhs = (t⋆u4)⋆uu, rhs = t⋆uu
      if (u1=u2) ∧ (u3=u4) ∧ (u5=u6) ∧ (u1=u3) ∧ (u1=u5) then
        [Term.op t (Term.op u1 u1)]
      else []
  | RuleId.DoubleSq, _ => []

/-- all one-step generator successors under a RuleSet (context-closed) -/
def genNext {α : Type} [DecidableEq (Term α)] (R : RuleSet) : Term α → List (Term α)
  | Term.var _ => []
  | Term.op t u =>
      let here :=
        lbind R (fun rid => genRoot rid (Term.op t u))
      eraseDups (
        here
        ++ (genNext R t).map (fun t' => Term.op t' u)
        ++ (genNext R u).map (fun u' => Term.op t u')
      )

/-- filter a successor list by size bound K and universe list U -/
def bounded {α : Type} [DecidableEq (Term α)] (K : Nat) (U : List (Term α)) (xs : List (Term α)) : List (Term α) :=
  xs.filter (fun t => (tsize t ≤ K) && (t ∈ U))

/-- undirected neighbors induced by a directed next function within U -/
def neighborsUndir {α : Type} [DecidableEq (Term α)]
  (K : Nat) (U : List (Term α)) (next : Term α → List (Term α)) (t : Term α) : List (Term α) :=
  let fwd := bounded K U (next t)
  let bwd := U.filter (fun u => t ∈ bounded K U (next u))
  eraseDups (fwd ++ bwd)

/-- BFS with fuel (core-only) -/
partial def bfsFuel {α : Type} [DecidableEq α]
  (fuel : Nat) (next : α → List α) (queue visited : List α) : List α :=
  match fuel with
  | 0 => visited
  | fuel+1 =>
      match queue with
      | [] => visited
      | x :: q =>
          if x ∈ visited then
            bfsFuel fuel next q visited
          else
            bfsFuel fuel next (q ++ next x) (x :: visited)

/-- connected component within bound -/
def component {α : Type} [DecidableEq α]
  (fuel : Nat) (next : α → List α) (start : α) : List α :=
  bfsFuel fuel next [start] []

def connected {α : Type} [DecidableEq α]
  (fuel : Nat) (next : α → List α) (a b : α) : Bool :=
  b ∈ component fuel next a

/-- Association-list lookup (core-only). -/
def assocFind? {α β : Type} [DecidableEq α] (a : α) : List (α × β) → Option β
  | [] => none
  | (k, v) :: xs => if k = a then some v else assocFind? a xs

/-- True iff key `a` is present in association list. -/
def hasKey {α β : Type} [DecidableEq α] (a : α) (m : List (α × β)) : Bool :=
  (assocFind? (α := α) (β := β) a m).isSome

/--
BFS that records a predecessor map for a shortest path from `start` to `target`
in the (implicit) graph given by `next` (core-only).
Returns an association list `pred` mapping each discovered node to its parent.
-/
partial def bfsPred {α : Type} [DecidableEq α]
  (fuel : Nat) (next : α → List α) (target : α)
  (queue visited : List α) (pred : List (α × α)) : Option (List (α × α)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      match queue with
      | [] => none
      | x :: q =>
          if x = target then
            some pred
          else if x ∈ visited then
            bfsPred fuel next target q visited pred
          else
            let fresh :=
              (next x).filter (fun y =>
                !(y ∈ visited) && !(y ∈ q) && !(hasKey (α := α) (β := α) y pred))
            let pred' := fresh.foldl (fun pr y => (y, x) :: pr) pred
            bfsPred fuel next target (q ++ fresh) (x :: visited) pred'

/-- Reconstruct a path from `start` to `target` using predecessor map `pred`. -/
partial def buildPath {α : Type} [DecidableEq α]
  (fuel : Nat) (pred : List (α × α)) (start target : α) : Option (List α) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if target = start then
        some [start]
      else
        match assocFind? (α := α) (β := α) target pred with
        | none => none
        | some p =>
            match buildPath fuel pred start p with
            | none => none
            | some ps => some (ps ++ [target])

/-- Shortest path (as a list of vertices) between `a` and `b`, if it exists. -/
def pathBetween {α : Type} [DecidableEq α]
  (fuel : Nat) (next : α → List α) (a b : α) : Option (List α) :=
  if a = b then
    some [a]
  else
    match bfsPred (α := α) fuel next b [a] [] [] with
    | none => none
    | some pred => buildPath (α := α) fuel pred a b

/--
Like `findGap`, but also returns a concrete *Red* path witnessing connectivity
in the undirected Red-graph within bound `K`.
The path may go through non-normal terms (this is the point: it explains the peak).
-/
def findGapWithRedPath (K : Nat) (R : RuleSet := defaultRules) :
  Option (Term V × Term V × List (Term V)) :=
  let U := eraseDups (termsUpTo K)
  let fuel := (U.length + 1) * (U.length + 1)
  let redN  := fun t => neighborsUndir (α := V) K U (redNext (α := V)) t
  let genN  := fun t => neighborsUndir (α := V) K U (genNext (α := V) R) t
  let normals := U.filter (fun t => isNormal (α := V) t)

  -- nested search (same policy as `findGap`)
  let rec outer : List (Term V) → Option (Term V × Term V × List (Term V))
    | [] => none
    | u :: us =>
        let rec inner : List (Term V) → Option (Term V × Term V × List (Term V))
          | [] => none
          | v :: vs =>
              if u = v then inner vs else
              if connected fuel redN u v && !(connected fuel genN u v) then
                match pathBetween (α := Term V) fuel redN u v with
                | some p => some (u, v, p)
                | none   => none
              else
                inner vs
        match inner normals with
        | some p => some p
        | none   => outer us

  outer normals


def findGapWithRedPathAfter (K : Nat) (skip : Nat) (R : RuleSet := defaultRules) :
  Option (Term V × Term V × List (Term V)) :=
  let U := eraseDups (termsUpTo K)
  let fuel := (U.length + 1) * (U.length + 1)
  let redN  := fun t => neighborsUndir (α := V) K U (redNext (α := V)) t
  let genN  := fun t => neighborsUndir (α := V) K U (genNext (α := V) R) t
  let normals := U.filter (fun t => isNormal (α := V) t)

  -- inner returns (remainingSkip, found?)
  let rec inner (u : Term V) (k : Nat) : List (Term V) → Nat × Option (Term V × Term V × List (Term V))
    | [] => (k, none)
    | v :: vs =>
        if u = v then
          inner u k vs
        else if connected fuel redN u v && !(connected fuel genN u v) then
          if k = 0 then
            match pathBetween (α := Term V) fuel redN u v with
            | some p => (0, some (u, v, p))
            | none   => (0, none)   -- should not happen if `connected` was true
          else
            inner u (k - 1) vs
        else
          inner u k vs

  let rec outer (k : Nat) : List (Term V) → Option (Term V × Term V × List (Term V))
    | [] => none
    | u :: us =>
        let (k', res) := inner u k normals
        match res with
        | some r => some r
        | none   => outer k' us

  outer skip normals



/-! ############################################################
## Normal-only generator graph variants (peak-compression aligned)
############################################################ -/

/--
`findGapWithRedPath` variant where the **generator graph is restricted to NORMAL nodes**.

Interpretation:
- Red connectivity is checked in the full bounded universe `U` (so a witness may go through non-normal terms).
- Generator connectivity is checked **only among normal terms** using direct one-step generator edges
  (Normal → Normal “shortcuts” only).

This matches the “peak compression” viewpoint:
adding generators should create shortcuts that bypass non-normal excursions.
-/
def findGapWithRedPathNFGen (K : Nat) (R : RuleSet := defaultRules) :
  Option (Term V × Term V × List (Term V)) :=
  let U := eraseDups (termsUpTo K)
  let normals := U.filter (fun t => isNormal (α := V) t)

  let fuelRed := (U.length + 1) * (U.length + 1)
  let fuelGen := (normals.length + 1) * (normals.length + 1)

  let redN  := fun t => neighborsUndir (α := V) K U (redNext (α := V)) t
  let genNn := fun t => neighborsUndir (α := V) K normals (genNext (α := V) R) t

  let rec outer : List (Term V) → Option (Term V × Term V × List (Term V))
    | [] => none
    | u :: us =>
        let rec inner : List (Term V) → Option (Term V × Term V × List (Term V))
          | [] => none
          | v :: vs =>
              if u = v then inner vs else
              if connected fuelRed redN u v && !(connected fuelGen genNn u v) then
                match pathBetween (α := Term V) fuelRed redN u v with
                | some p => some (u, v, p)
                | none   => none
              else
                inner vs
        match inner normals with
        | some p => some p
        | none   => outer us

  outer normals

/-- “skip the first `skip` many gaps” version of `findGapWithRedPathNFGen`. -/
def findGapWithRedPathAfterNFGen (K : Nat) (skip : Nat) (R : RuleSet := defaultRules) :
  Option (Term V × Term V × List (Term V)) :=
  let U := eraseDups (termsUpTo K)
  let normals := U.filter (fun t => isNormal (α := V) t)

  let fuelRed := (U.length + 1) * (U.length + 1)
  let fuelGen := (normals.length + 1) * (normals.length + 1)

  let redN  := fun t => neighborsUndir (α := V) K U (redNext (α := V)) t
  let genNn := fun t => neighborsUndir (α := V) K normals (genNext (α := V) R) t

  let rec inner (u : Term V) (k : Nat) : List (Term V) → Nat × Option (Term V × Term V × List (Term V))
    | [] => (k, none)
    | v :: vs =>
        if u = v then
          inner u k vs
        else if connected fuelRed redN u v && !(connected fuelGen genNn u v) then
          if k = 0 then
            match pathBetween (α := Term V) fuelRed redN u v with
            | some p => (0, some (u, v, p))
            | none   => (0, none)
          else
            inner u (k - 1) vs
        else
          inner u k vs

  let rec outer (k : Nat) : List (Term V) → Option (Term V × Term V × List (Term V))
    | [] => none
    | u :: us =>
        let (k', res) := inner u k normals
        match res with
        | some r => some r
        | none   => outer k' us

  outer skip normals

def findGapAfterNFGen_fast (K : Nat) (skip : Nat) (R : RuleSet := defaultRules) :
  Option (Term V × Term V) :=
  let U := eraseDups (termsUpTo K)
  let normals := U.filter (fun t => isNormal (α := V) t)

  let fuelRed := (U.length + 1) * (U.length + 1)
  let fuelGen := (normals.length + 1) * (normals.length + 1)

  let redN  := fun t => neighborsUndir (α := V) K U      (redNext (α := V)) t
  let genNn := fun t => neighborsUndir (α := V) K normals (genNext (α := V) R) t

  let rec goU (us : List (Term V)) (k : Nat) : Option (Term V × Term V) :=
    match us with
    | [] => none
    | u :: us =>
        let rec goV (vs : List (Term V)) (k : Nat) : Option (Term V × Term V) :=
          match vs with
          | [] => goU us k
          | v :: vs =>
              if u = v then
                goV vs k
              else if connected fuelRed redN u v && !(connected fuelGen genNn u v) then
                match k with
                | 0 => some (u, v)
                | Nat.succ k' => goV vs k'
              else
                goV vs k
        goV normals k
  goU normals skip

/-! ############################################################
## N-optimization helpers: collect many gaps with ONE graph build
############################################################ -/

/-- Build connected-component ids for an undirected graph given by neighbors. -/
private def compIds
  (fuel : Nat)
  (nodes : List (Term V))
  (neigh : Term V → List (Term V)) : Term V → Nat :=
by
  -- BFS with explicit fuel
  let rec bfs (fuel : Nat) (q : List (Term V)) (seen : List (Term V)) : List (Term V) :=
    match fuel with
    | 0 => seen
    | fuel+1 =>
        match q with
        | [] => seen
        | a :: qs =>
            if seen.contains a then
              bfs fuel qs seen
            else
              bfs fuel (neigh a ++ qs) (a :: seen)

  -- build table term -> component id
  let rec go (fuel : Nat) (todo : List (Term V)) (cid : Nat) (acc : List (Term V × Nat)) :
      List (Term V × Nat) :=
    match fuel with
    | 0 => acc
    | fuel+1 =>
        match todo with
        | [] => acc
        | t :: ts =>
            if (acc.any (fun p => p.1 = t)) then
              go fuel ts cid acc
            else
              let comp := bfs fuel [t] []
              let acc' := comp.foldl (init := acc) (fun a x => (x, cid) :: a)
              go fuel ts (cid+1) acc'

  let table := go fuel nodes 1 []
  exact fun t =>
    match table.find? (fun p => p.1 = t) with
    | some p => p.2
    | none   => 0

/--
Collect first N gap witnesses (u,v) with ONE graph build.
This is what you want for (i): just get witness pairs fast.
-/
def firstNGapsAfterNFGen (K N : Nat) (R : RuleSet := defaultRules) :
  List (Term V × Term V) :=
  let U := eraseDups (termsUpTo K)
  let normals := U.filter (fun t => isNormal (α := V) t)

  let redN  := fun t => neighborsUndir (α := V) K U      (redNext (α := V)) t
  let genNn := fun t => neighborsUndir (α := V) K normals (genNext (α := V) R) t

  -- components (computed once)
  let redId := compIds (fuel := (U.length+1)*(U.length+1)) U redN
  let genId := compIds (fuel := (normals.length+1)*(normals.length+1)) normals genNn

  -- scan pairs and collect up to N
  let rec outer (us : List (Term V)) (acc : List (Term V × Term V)) : List (Term V × Term V) :=
    match us with
    | [] => acc.reverse
    | u :: us =>
        if acc.length = N then
          acc.reverse
        else
          let rec inner (vs : List (Term V)) (acc : List (Term V × Term V)) :=
            match vs with
            | [] => acc
            | v :: vs =>
                if acc.length = N then acc
                else if u = v then inner vs acc
                else if redId u = redId v && genId u ≠ genId v then
                  inner vs ((u,v) :: acc)
                else
                  inner vs acc
          outer us (inner normals acc)

  outer normals []
/-- search for a NORMAL gap: Red-connected but Gen-not-connected -/
def findGap (K : Nat) (R : RuleSet := defaultRules) : Option (Term V × Term V) :=
  let U := eraseDups (termsUpTo K)
  let fuel := (U.length + 1) * (U.length + 1)
  let redN  := fun t => neighborsUndir (α := V) K U (redNext (α := V)) t
  let genN  := fun t => neighborsUndir (α := V) K U (genNext (α := V) R) t

  let normals := U.filter (fun t => isNormal (α := V) t)

  -- nested search
  let rec outer : List (Term V) → Option (Term V × Term V)
    | [] => none
    | u :: us =>
        let rec inner : List (Term V) → Option (Term V × Term V)
          | [] => none
          | v :: vs =>
              if u = v then inner vs else
              if connected fuel redN u v && !(connected fuel genN u v) then
                some (u, v)
              else
                inner vs
        match inner normals with
        | some p => some p
        | none   => outer us

  outer normals

/-- pretty printer for `Term V` where `V := Fin 1` (so only one variable). -/
def termStr : Term V → String
  | .var _   => "x"--| .var i => "x" ++ toString i.1
  | .op a b  => "(" ++ termStr a ++ "⋆" ++ termStr b ++ ")"

/-- Pretty printer for contexts (shows a hole). -/
def ctxStr : Ctx V → String
  | .hole => "□"
  | .left C r  => "(" ++ ctxStr C ++ "⋆" ++ termStr r ++ ")"
  | .right l C => "(" ++ termStr l ++ "⋆" ++ ctxStr C ++ ")"

/-
Strip a (deterministically chosen) common outer context from two terms.

If both are `op` and share the same left child, strip on the right (wrap with `Ctx.right`).
Else if they share the same right child, strip on the left (wrap with `Ctx.left`).
Otherwise stop.

This gives you a *consistent* notion of “core pair” for classification.
-/
def stripCommonCtx {α : Type} [DecidableEq α] :
  Term α → Term α → (Ctx α × Term α × Term α)
  | .op u1 u2, .op v1 v2 =>
    if u1 = v1 && u2 = v2 then -- u = v のケース
      (Ctx.hole, .op u1 u2, .op v1 v2)
    else if u1 = v1 then
      let (C, a, b) := stripCommonCtx u2 v2
      (Ctx.right u1 C, a, b)
    else if u2 = v2 then
      let (C, a, b) := stripCommonCtx u1 v1
      (Ctx.left C u2, a, b)
    else
      (Ctx.hole, .op u1 u2, .op v1 v2)
  | u, v => (Ctx.hole, u, v)

def stripCommonCtxDepth {α : Type} [DecidableEq α] :
  Nat → Term α → Term α → (Ctx α × Term α × Term α)
  | 0, u, v => (Ctx.hole, u, v)
  | Nat.succ d, .op u1 u2, .op v1 v2 =>
      if u1 = v1 then
        let (C, a, b) := stripCommonCtxDepth d u2 v2
        (Ctx.right u1 C, a, b)
      else if u2 = v2 then
        let (C, a, b) := stripCommonCtxDepth d u1 v1
        (Ctx.left C u2, a, b)
      else
        (Ctx.hole, .op u1 u2, .op v1 v2)
  | Nat.succ _, u, v => (Ctx.hole, u, v)

/-! ############################################################
## Canonical stripping + context/orbit exploration helpers
############################################################ -/

/--
Strip a common outer context **as far as possible** (canonical “core pair”),
by using a depth bound large enough for the given terms.
This is a convenience wrapper around `stripCommonCtxDepth`.
-/
def stripCommonCtxAll {α : Type} [DecidableEq α] (u v : Term α) : (Ctx α × Term α × Term α) :=
  stripCommonCtxDepth (α := α) (tsize u + tsize v) u v

/-- Plug a term into a context (local, core-only; matches `ctxStr`). -/
def plugCtx : Ctx V → Term V → Term V
  | .hole, t       => t
  | .left C r, t   => Term.op (plugCtx C t) r
  | .right l C, t  => Term.op l (plugCtx C t)

/-- Depth of a context (number of wrappers around the hole). -/
def ctxDepth : Ctx V → Nat
  | .hole        => 0
  | .left C _    => ctxDepth C + 1
  | .right _ C   => ctxDepth C + 1

/-- Deduplicate contexts by their pretty-printed string `ctxStr`. -/
def eraseDupsCtx (cs : List (Ctx V)) : List (Ctx V) :=
  let rec go (seen : List String) : List (Ctx V) → List (Ctx V)
    | []      => []
    | c :: cs =>
        let k := ctxStr c
        if k ∈ seen then
          go seen cs
        else
          c :: go (k :: seen) cs
  go [] cs

/-- Base terms for building contexts: all terms up to `Kbase` (deduplicated). -/
def baseTerms (Kbase : Nat) : List (Term V) :=
  eraseDups (termsUpTo Kbase)

/--
Enumerate contexts up to a given `depth`, using a small list of “filler” terms.

This is meant for **orbit exploration**:
how a fixed core pair `(u,v)` reappears under different outer contexts.
-/
def ctxsUpTo (depth : Nat) (fillers : List (Term V)) : List (Ctx V) :=
  let rec build : Nat → List (Ctx V) → List (Ctx V)
    | 0, acc => eraseDupsCtx acc
    | Nat.succ d, acc =>
        let next :=
          acc ++ lbind acc (fun C =>
            lbind fillers (fun t => [Ctx.left C t, Ctx.right t C]))
        build d next
  build depth [Ctx.hole]

/--
Contexts (up to `depth`, built from terms up to `Kbase`) that preserve normality
for both endpoints `u` and `v` (after plugging).
-/
def ctxsPreservingNormal (Kbase depth : Nat) (u v : Term V) : List (Ctx V) :=
  let fillers := baseTerms Kbase
  (ctxsUpTo depth fillers).filter (fun C =>
    isNormal (plugCtx C u) && isNormal (plugCtx C v))

/-- Same as `ctxsPreservingNormal`, but also enforces the global size bound `K` after plugging. -/
def ctxsPreservingNormalBounded (K Kbase depth : Nat) (u v : Term V) : List (Ctx V) :=
  (ctxsPreservingNormal Kbase depth u v).filter (fun C =>
    (tsize (plugCtx C u) ≤ K) && (tsize (plugCtx C v) ≤ K))

/--
Given a known “core” pair `(u,v)`, search for outer contexts (within small bounds)
that reproduce a **gap** under the normal-only generator notion:

- `plugCtx C u` and `plugCtx C v` are normal and size-bounded,
- Red-connected in the full universe `U`,
- but NOT generator-connected in the normal-only generator graph.

This is an inexpensive way to study “why K increases cause new ctx variants”:
they are exactly the contexts that preserve normality and keep the gap visible.
-/
def orbitGapContextsNFGen
  (K : Nat) (Kbase depth : Nat) (R : RuleSet)
  (u v : Term V) : List String :=
  let U := eraseDups (termsUpTo K)
  let normals := U.filter (fun t => isNormal (α := V) t)

  let fuelRed := (U.length + 1) * (U.length + 1)
  let fuelGen := (normals.length + 1) * (normals.length + 1)

  let redN  := fun t => neighborsUndir (α := V) K U (redNext (α := V)) t
  let genNn := fun t => neighborsUndir (α := V) K normals (genNext (α := V) R) t

  let cs := ctxsPreservingNormalBounded K Kbase depth u v

  lbind cs (fun C =>
    let u' := plugCtx C u
    let v' := plugCtx C v
    if (u' ∈ normals) && (v' ∈ normals)
        && connected fuelRed redN u' v'
        && !(connected fuelGen genNn u' v') then
      ["ctx=" ++ ctxStr C ++ " | u=" ++ termStr u' ++ " | v=" ++ termStr v']
    else
      [])

def termListStr (xs : List (Term V)) : String :=
  "[" ++ String.intercalate ", " (xs.map termStr) ++ "]"

def gapStr : Option (Term V × Term V) → String
  | none => "none"
  | some (u, v) => "some (" ++ termStr u ++ ", " ++ termStr v ++ ")"

def gapWithPathStr : Option (Term V × Term V × List (Term V)) → String
  | none => "none"
  | some (u, v, p) =>
      "some (" ++ termStr u ++ ", " ++ termStr v ++ ", " ++ termListStr p ++ ")"


/-! ############################################################
## Peak (non-normal excursion) observation helpers
############################################################ -/

/-- Boolean normality test (computed via `redNext`): `true` iff the term has no one-step Red successor. -/
def isNormalB (t : Term V) : Bool :=
  isNormal (α := V) t

/-- Internal state machine for extracting non-normal excursions along a Red-path. -/
private inductive PEState where
  | nonePrev
  | outside (prevNormal : Term V)
  | inside (startNormal : Term V) (midRev : List (Term V))
deriving Repr

/--
Extract “peak excursions” from a concrete Red-path `p` (a list of vertices).

Each excursion is returned as `(startNormal, mids, endNormal)` where:
- `startNormal` and `endNormal` are normal terms,
- `mids` is a non-empty list of **non-normal** terms appearing between them in the path.

This matches the “peak compression” viewpoint:
a RedEq witness can leave the normal world and later return.
-/
def peakExcursions (p : List (Term V)) : List (Term V × List (Term V) × Term V) :=
  let rec go : PEState → List (Term V) → List (Term V × List (Term V) × Term V)
    | .nonePrev, [] => []
    | .nonePrev, t :: ts =>
        if isNormalB t then
          go (.outside t) ts
        else
          go .nonePrev ts
    | .outside _prev, [] => []
    | .outside prev, t :: ts =>
        if isNormalB t then
          go (.outside t) ts
        else
          go (.inside prev [t]) ts
    | .inside _start _midRev, [] => []
    | .inside start midRev, t :: ts =>
        if isNormalB t then
          (start, midRev.reverse, t) :: go (.outside t) ts
        else
          go (.inside start (t :: midRev)) ts
  go .nonePrev p

/-- First excursion, if any. -/
def firstPeakExcursion? (p : List (Term V)) : Option (Term V × List (Term V) × Term V) :=
  (peakExcursions p).head?

/-- Pretty-print excursions (for `#eval` usage). -/
def peakExcursionsStr (p : List (Term V)) : String :=
  let one (e : Term V × List (Term V) × Term V) : String :=
    match e with
    | (s, mids, t) =>
        "start=" ++ termStr s
        ++ " mids=" ++ termListStr mids
        ++ " end=" ++ termStr t
  "[" ++ String.intercalate "; " ((peakExcursions p).map one) ++ "]"


/-- Explain a *root* C1 or C2p step, if `a → b` is exactly one root rewrite. -/
def explainRoot? : Term V → Term V → Option String
  -- 先により具体的な（深い）パターンを置く
  | .op (.op (.op x y) z) (.op y' z'), b =>
      if y' = y && z' = z && b = (.op (.op x y) z) then
        some "C2p@root"
      else
        none
  -- 次に一般的なパターンを置く
  | .op (.op x y) y', b =>
      if y' = y && b = (.op x y) then
        some "C1@root"
      else
        none
  | _, _ => none

/--
Explain a one-step `Red` move `a → b` by locating the redex position.
We return strings like:
- "C1@root", "C2p@root"
- "left(C1@root)", "right(left(C2p@root))", ...
-/
partial def explainRedDir? : Term V → Term V → Option String
  | a, b =>
      match explainRoot? a b with
      | some s => some s
      | none =>
        match a, b with
        | .op a1 a2, .op b1 b2 =>
            -- exactly one side changes for a 1-step context closure
            if a2 = b2 then
              match explainRedDir? a1 b1 with
              | some s => some ("left(" ++ s ++ ")")
              | none   => none
            else if a1 = b1 then
              match explainRedDir? a2 b2 with
              | some s => some ("right(" ++ s ++ ")")
              | none   => none
            else
              none
        | _, _ => none

/-- Explain an undirected edge between consecutive nodes in a path. -/
def explainEdge (a b : Term V) : String :=
  match explainRedDir? a b with
  | some s => "→[" ++ s ++ "]"
  | none =>
    match explainRedDir? b a with
    | some s => "←[" ++ s ++ "]"
    | none   => "→[?]"

/-- Turn a path `[t0,t1,...,tk]` into annotated lines. -/
def pathTaggedLines : List (Term V) → List String
  | [] => []
  | [_] => []
  | a :: b :: rest =>
      (termStr a ++ " " ++ explainEdge a b ++ " " ++ termStr b)
      :: pathTaggedLines (b :: rest)

/-- Pretty-print `findGapWithRedPath` with step annotations. -/
def gapWithTaggedPathStr :
  Option (Term V × Term V × List (Term V)) → String
  | none => "none"
  | some (u, v, p) =>
      "u = " ++ termStr u ++ "\n"
      ++ "v = " ++ termStr v ++ "\n"
      ++ "path:\n"
      ++ String.intercalate "\n" (pathTaggedLines p)
/-- Which side we stepped into while locating the redex. -/
inductive Dir where
  | left | right
deriving DecidableEq, Repr

def dirChar : Dir → String
  | .left  => "L"
  | .right => "R"

/-- Render a position as root / L / LR / LRL ... -/
def posStr (pos : List Dir) : String :=
  match pos with
  | [] => "root"
  | _  => String.intercalate "" (pos.map dirChar)

def depth (pos : List Dir) : Nat := pos.length

/-- Root rule kind. -/
inductive StepKind where
  | C1 | C2p
deriving DecidableEq, Repr

def kindStr : StepKind → String
  | .C1  => "C1"
  | .C2p => "C2p"

/-- Information extracted from a root redex match. -/
structure RootMatch where
  kind : StepKind
  x : Term V
  y : Term V
  z : Option (Term V) := none
deriving Repr

def rootMatchStr (m : RootMatch) : String :=
  match m.kind, m.z with
  | .C1, none =>
      "(" ++ "x:=" ++ termStr m.x ++ ", y:=" ++ termStr m.y ++ ")"
  | .C2p, some z =>
      "(" ++ "x:=" ++ termStr m.x ++ ", y:=" ++ termStr m.y ++ ", z:=" ++ termStr z ++ ")"
  | _, _ =>
      "(ill-formed)"  -- should not happen

/-- Check whether `a → b` is exactly one root C1 or C2p step, and extract (x,y,z). -/
def explainRootMatch? : Term V → Term V → Option RootMatch
  -- 1. より具体的（複雑）な構造を先に判定
  | .op (.op (.op x y) z) (.op y' z'), b =>
      if y' = y && z' = z && b = (.op (.op x y) z) then
        some { kind := .C2p, x := x, y := y, z := some z }
      else
        none
  -- 2. より一般的（単純）な構造を次に判定
  | .op (.op x y) y', b =>
      if y' = y && b = (.op x y) then
        some { kind := .C1, x := x, y := y }
      else
        none
  -- 3. いずれにもマッチしない場合
  | _, _ => none

/--
Explain a directed one-step `Red` move `a → b` by locating the redex position
and extracting the matched root parameters.
Returns (pos, rootMatch).
-/
partial def explainRedDirInfo? : Term V → Term V → Option (List Dir × RootMatch)
  | a, b =>
      match explainRootMatch? a b with
      | some m => some ([], m)
      | none =>
        match a, b with
        | .op a1 a2, .op b1 b2 =>
            -- exactly one side changes for a 1-step context closure
            if a2 = b2 then
              match explainRedDirInfo? a1 b1 with
              | some (pos, m) => some (Dir.left :: pos, m)
              | none => none
            else if a1 = b1 then
              match explainRedDirInfo? a2 b2 with
              | some (pos, m) => some (Dir.right :: pos, m)
              | none => none
            else
              none
        | _, _ => none

/-- Format an edge annotation like: C2p@LR depth=2 (x:=...,y:=...,z:=...) -/
def annotStr (pos : List Dir) (m : RootMatch) : String :=
  kindStr m.kind
  ++ "@"
  ++ posStr pos
  ++ " depth="
  ++ toString (depth pos)
  ++ " "
  ++ rootMatchStr m

/-- Explain an undirected edge between consecutive nodes in a path, with depth and match params. -/
def explainEdge2 (a b : Term V) : String :=
  match explainRedDirInfo? a b with
  | some (pos, m) => "→[" ++ annotStr pos m ++ "]"
  | none =>
    match explainRedDirInfo? b a with
    | some (pos, m) => "←[" ++ annotStr pos m ++ "]"
    | none => "→[?]"

/-- Turn a path `[t0,t1,...,tk]` into annotated lines. -/
def pathTaggedLines2 : List (Term V) → List String
  | [] => []
  | [_] => []
  | a :: b :: rest =>
      (termStr a ++ " " ++ explainEdge2 a b ++ " " ++ termStr b)
      :: pathTaggedLines2 (b :: rest)

/-- Pretty-print `findGapWithRedPath` with detailed step annotations. -/
def gapWithTaggedPathStr2 :
  Option (Term V × Term V × List (Term V)) → String
  | none => "none"
  | some (u, v, p) =>
      "u = " ++ termStr u ++ "\n"
      ++ "v = " ++ termStr v ++ "\n"
      ++ "path:\n"
      ++ String.intercalate "\n" (pathTaggedLines2 p)

def gapWithTaggedPathStr3 :
  Option (Term V × Term V × List (Term V)) → String
  | none => "none"
  | some (u, v, p) =>
      -- 燃料として (tsize u + tsize v) などを渡す
      let (C, u0, v0) := stripCommonCtxDepth (tsize u + tsize v) u v
      "ctx = " ++ ctxStr C ++ "\n"
      ++ "core u = " ++ termStr u0 ++ "\n"
      ++ "core v = " ++ termStr v0 ++ "\n"
      ++ "u = " ++ termStr u ++ "\n"
      ++ "v = " ++ termStr v ++ "\n"
      ++ "path:\n"
      ++ String.intercalate "\n" (pathTaggedLines2 p)

/-- Observation package for a gap: context + cores + original pair + a concrete Red path. -/
structure GapObs where
  ctx   : Ctx V
  coreU : Term V
  coreV : Term V
  u     : Term V
  v     : Term V
  path  : List (Term V)
deriving Repr

/-- Build `GapObs` using an explicit stripping function. -/
def mkGapObsWith
  (stripFn : Term V → Term V → (Ctx V × Term V × Term V))
  (u v : Term V) (p : List (Term V)) : GapObs :=
  let (C, u0, v0) := stripFn u v
  { ctx := C, coreU := u0, coreV := v0, u := u, v := v, path := p }

/-- Default builder: uses `stripCommonCtx` (your current choice). -/
def mkGapObs (u v : Term V) (p : List (Term V)) : GapObs :=
  mkGapObsWith (stripFn := stripCommonCtx (α := V)) u v p

/-- Convert `Option (u,v,path)` into `Option GapObs` using a chosen strip function. -/
def gapObsFrom
  (stripFn : Term V → Term V → (Ctx V × Term V × Term V))
  : Option (Term V × Term V × List (Term V)) → Option GapObs
  | none => none
  | some (u, v, p) => some (mkGapObsWith stripFn u v p)

/-- Pretty-print a `GapObs`. -/
def gapObsStr (g : GapObs) : String :=
  "ctx = " ++ ctxStr g.ctx ++ "\n"
  ++ "core u = " ++ termStr g.coreU ++ "\n"
  ++ "core v = " ++ termStr g.coreV ++ "\n"
  ++ "u = " ++ termStr g.u ++ "\n"
  ++ "v = " ++ termStr g.v ++ "\n"
  ++ "path:\n"
  ++ String.intercalate "\n" (pathTaggedLines2 g.path)

/-- Pretty-print an optional gap, by first packaging it into `GapObs`. -/
def gapObsStrFrom
  (stripFn : Term V → Term V → (Ctx V × Term V × Term V))
  (o : Option (Term V × Term V × List (Term V))) : String :=
  match gapObsFrom (stripFn := stripFn) o with
  | none => "none"
  | some g => gapObsStr g

def normCorePair (u v : Term V) : Term V × Term V :=
  match compare (termStr u) (termStr v) with
  | Ordering.gt => (v, u)
  | _           => (u, v)

def coreSig (g : GapObs) : String :=
  let (u0, v0) := normCorePair g.coreU g.coreV
  "ctx=" ++ ctxStr g.ctx
  ++ " | core=(" ++ termStr u0 ++ " , " ++ termStr v0 ++ ")"

def collectGapObs
  (K : Nat) (howMany : Nat) (stripFn : Term V → Term V → (Ctx V × Term V × Term V))
  (R : RuleSet := defaultRules) : List GapObs :=
  let rec go (i : Nat) (acc : List GapObs) : List GapObs :=
    if acc.length >= howMany then acc else
    match findGapWithRedPathAfter K i (R := R) with
    | none => acc
    | some (u,v,p) =>
        let g := mkGapObsWith (stripFn := stripFn) u v p
        go (i+1) (g :: acc)
  go 0 []

def collectCoreSigs (K howMany : Nat)
  (stripFn : Term V → Term V → (Ctx V × Term V × Term V))
  (R : RuleSet := defaultRules) : List String :=
  (collectGapObs K howMany stripFn (R := R)).reverse.map coreSig

/-! ############################################################
## Normal-only generator variants for batch collection
############################################################ -/

/-- Collect `GapObs` using `findGapWithRedPathAfterNFGen` (normal-only generator notion). -/
def collectGapObsNFGen
  (K : Nat) (howMany : Nat) (stripFn : Term V → Term V → (Ctx V × Term V × Term V))
  (R : RuleSet := defaultRules) : List GapObs :=
  let rec go (i : Nat) (acc : List GapObs) : List GapObs :=
    if acc.length >= howMany then acc else
    match findGapWithRedPathAfterNFGen K i (R := R) with
    | none => acc
    | some (u, v, p) =>
        let g := mkGapObsWith (stripFn := stripFn) u v p
        go (i + 1) (g :: acc)
  go 0 []

/-- Collect “core signatures” using the normal-only generator notion. -/
def collectCoreSigsNFGen (K howMany : Nat)
  (stripFn : Term V → Term V → (Ctx V × Term V × Term V))
  (R : RuleSet := defaultRules) : List String :=
  (collectGapObsNFGen K howMany stripFn (R := R)).reverse.map coreSig

/-! ############################################################
## Convenience collectors (canonical strip + normalized coreSig)
############################################################ -/

/-- Collect core signatures using `stripCommonCtxAll` (maximal stripping). -/
def collectCoreSigsNFGenAll (K howMany : Nat)
  (R : RuleSet := defaultRules) : List String :=
  collectCoreSigsNFGen (K := K) (howMany := howMany)
    (stripFn := fun u v => stripCommonCtxAll (α := V) u v)
    (R := R)

/-- Same as `collectCoreSigsNFGenAll`, but deduplicates identical signatures. -/
def collectCoreSigsNFGenAllUnique (K howMany : Nat)
  (R : RuleSet := defaultRules) : List String :=
  eraseDups (collectCoreSigsNFGenAll (K := K) (howMany := howMany) (R := R))


/-
#eval WeakAbsorption.SmallCheck.gapObsStrFrom
  (stripFn := fun u v => WeakAbsorption.SmallCheck.stripCommonCtxDepth (α := WeakAbsorption.SmallCheck.V) 1 u v)
  (WeakAbsorption.SmallCheck.findGapWithRedPathAfter 3 1
    (R := [WeakAbsorption.Spec.RuleId.SqAbsorb]))-/
/-
#eval WeakAbsorption.SmallCheck.collectCoreSigs
  13 20
  (stripFn := fun u v => WeakAbsorption.SmallCheck.stripCommonCtxDepth (α := WeakAbsorption.SmallCheck.V) 1 u v)
  (R := [WeakAbsorption.Spec.RuleId.SqAbsorb])-/

end SmallCheck
end WeakAbsorption
