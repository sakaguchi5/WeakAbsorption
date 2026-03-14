import WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.DoubleSq_R4_SemanticPackage

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Necessity

open WeakAbsorption
open WeakAbsorption.Closure
open WeakAbsorption.Spec
open WeakAbsorption.WAA
open WeakAbsorption.Proof.Generators.Vars1
open WeakAbsorption.Proof.Generators.Vars1.Independence.Witness
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity
open WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.ProofCore

section RowCoordinates

/-- Purely presentational row slots. This layer does not carry semantics by itself. -/
inductive RowSlot where
  | sqAbsorb
  | sqStable
  | decor
  | c2c1
deriving DecidableEq, Repr

/-- One atomic coordinate in the exact-row presentation layer. -/
structure RowAtom where
  slot    : RowSlot
  channel : CtxChannel
  tag     : CtxNFTag
deriving DecidableEq, Repr

/-- Expand one purified profile into atomic coordinates. -/
def rowAtomsOfProfile (slot : RowSlot) (p : PurifiedCtxProfile) : List RowAtom :=
  match p.channel? with
  | none => []
  | some ch => p.tags.map (fun tag => { slot := slot, channel := ch, tag := tag })

/-- Expand one exact row into atomic coordinates. -/
def rowAtomsOfRow (row : PurifiedCtxRow) : List RowAtom :=
  rowAtomsOfProfile .sqAbsorb row.sqAbsorb ++
  rowAtomsOfProfile .sqStable row.sqStable ++
  rowAtomsOfProfile .decor row.decor ++
  rowAtomsOfProfile .c2c1 row.c2c1

/-- Presentation-layer support of a target, read from its semantic package. -/
def rowAtomsOfTarget (tg : CoreKernelTarget) : List RowAtom :=
  rowAtomsOfRow (packageRow tg)

/-- Presentation-layer support of a realized state, read through `stateTarget`. -/
def rowAtomsOfState (σ : CoreRealizedState) : List RowAtom :=
  rowAtomsOfTarget (stateTarget σ)

theorem rowAtomsOfTarget_eq_of_packageRow (tg : CoreKernelTarget) :
    rowAtomsOfTarget tg = rowAtomsOfRow (corePurifiedRowOfTarget tg) := by
  simp [rowAtomsOfTarget, packageRow, package_row_eq]

theorem rowAtomsOfState_eq (σ : CoreRealizedState) :
    rowAtomsOfState σ = rowAtomsOfRow (corePurifiedRowOfTarget (stateTarget σ)) := by
  simp [rowAtomsOfState, rowAtomsOfTarget_eq_of_packageRow]

/-- The finite list of audited core targets. -/
def allCoreKernelTargets : List CoreKernelTarget :=
  [ .nfXASqRightPred
  , .nfUSqLiftRightSPred
  , .nfXADecorRightPred
  , .nfUDecorLiftRightSPred
  , .nfXADecorLeftPred
  , .nfUDecorLiftLeftSPred
  , .nfUStablePred
  , .nfUHolePred
  , .nfUDecorHolePred
  , .nfXASqAPred
  , .nfUSqLiftAPred
  , .nfUDecorRightPred ]

theorem mem_allCoreKernelTargets (tg : CoreKernelTarget) :
    tg ∈ allCoreKernelTargets := by
  cases tg <;> simp [allCoreKernelTargets]

/-- Semantic universe of atomic row coordinates that actually occur in the audited R4 core. -/
def exactRowAtomUniverse : List RowAtom :=
  (allCoreKernelTargets.flatMap rowAtomsOfTarget).eraseDups


private theorem mem_loop_of_mem_or_mem
    {α : Type u} [DecidableEq α]
    (r : α → α → Bool)
    (hr : ∀ x y, r x y = true ↔ x = y)
    {a : α} :
    ∀ (as bs : List α), a ∈ as ∨ a ∈ bs → a ∈ List.eraseDupsBy.loop r as bs := by
  intro as bs
  induction as generalizing bs
  case nil =>
    simp [List.eraseDupsBy.loop]
  case cons x xs ih =>
    simp [List.eraseDupsBy.loop]
    split
    case h_1 h_any =>
      have x_in_bs : x ∈ bs := by
        rcases List.any_eq_true.1 h_any with ⟨y, hy_bs, hy_r⟩
        have hxy : x = y := (hr x y).1 hy_r
        subst hxy
        exact hy_bs

      intro h_mem
      apply ih
      rcases h_mem with (h_as | h_bs)
      · rcases h_as with (rfl | h_xs)
        · exact Or.inr x_in_bs
        · exact Or.inl h_xs
      · exact Or.inr h_bs

    case h_2 h_any =>
      intro h_mem
      apply ih
      rcases h_mem with (h_as | h_bs)
      · rcases h_as with (rfl | h_xs)
        · exact Or.inr (List.Mem.head _)
        · exact Or.inl h_xs
      · exact Or.inr (List.Mem.tail _ h_bs)

theorem mem_of_mem_eraseDups {α : Type u} [DecidableEq α] {a : α} {l : List α} :
    a ∈ l → a ∈ l.eraseDups := by
  intro h
  unfold List.eraseDups
  apply mem_loop_of_mem_or_mem (r := fun x y => x == y)
  · -- hr の証明: r x y = true ↔ x = y
    intro x y
    simp [beq_iff_eq]
  · -- a ∈ l ∨ a ∈ [] の証明
    exact Or.inl h


theorem mem_exactRowAtomUniverse_of_mem_rowAtomsOfTarget
    {tg : CoreKernelTarget} {a : RowAtom}
    (ha : a ∈ rowAtomsOfTarget tg) :
    a ∈ exactRowAtomUniverse := by
  -- 1. 定義を展開して全体像を把握する
  rw [exactRowAtomUniverse]

  -- 2. eraseDups を適用しても要素の存在性は変わらないことを利用
  apply mem_of_mem_eraseDups

  -- 3. flatMap (List.bind) の要素存在条件に分解する
  -- a ∈ (L.flatMap f) ↔ ∃ x ∈ L, a ∈ f x
  apply List.mem_flatMap.2
  -- 4. 存在命題の証拠として tg を提示
  exists tg
  -- 5. 「tg が全ターゲットリストに含まれる」かつ「a がそのターゲットの Atom である」ことを示す
  constructor
  · -- tg ∈ allCoreKernelTargets の証明
    apply mem_allCoreKernelTargets
  · -- a ∈ rowAtomsOfTarget tg の証明
    exact ha



/-- exactRowAtomUniverse が重複を含まないことの証明 -/
theorem nodup_exactRowAtomUniverse : List.Nodup exactRowAtomUniverse := by
  decide  -- または単に decide

/-- ターゲットに含まれる Atom は必ず宇宙に含まれる -/
theorem rowAtomsOfTarget_subset_universe (tg : CoreKernelTarget) :
    ∀ a, a ∈ rowAtomsOfTarget tg → a ∈ exactRowAtomUniverse := by
  intro a ha
  exact mem_exactRowAtomUniverse_of_mem_rowAtomsOfTarget ha

theorem rowAtomsOfState_subset_universe (σ : CoreRealizedState) :
    ∀ a, a ∈ rowAtomsOfState σ → a ∈ exactRowAtomUniverse := by
  intro a ha
  exact mem_exactRowAtomUniverse_of_mem_rowAtomsOfTarget ha

/-- A fixed coordinate order for display. Semantics lives in `exactRowAtomUniverse`; this is only a basis order. -/
def exactRowAtomBasis : List RowAtom :=
  [ { slot := .sqAbsorb, channel := .right, tag := .nfXA }
  , { slot := .sqAbsorb, channel := .right, tag := .nfXASqRightPred }
  , { slot := .sqAbsorb, channel := .left,  tag := .nfU }
  , { slot := .sqAbsorb, channel := .left,  tag := .nfUSqLiftRightPred }
  , { slot := .sqAbsorb, channel := .root,  tag := .nfU }
  , { slot := .sqAbsorb, channel := .root,  tag := .nfUHolePred }
  , { slot := .sqAbsorb, channel := .left,  tag := .nfM }
  , { slot := .sqStable, channel := .left,  tag := .nfU }
  , { slot := .decor,    channel := .right, tag := .nfXA }
  , { slot := .decor,    channel := .left,  tag := .nfU }
  , { slot := .decor,    channel := .root,  tag := .nfU }
  , { slot := .decor,    channel := .right, tag := .nfU }
  , { slot := .c2c1,     channel := .root,  tag := .nfU } ]



/-- 表示用ベースの要素はすべて実際の宇宙に含まれる -/
theorem exactRowAtomBasis_subset_universe :
    ∀ a ∈ exactRowAtomBasis, a ∈ exactRowAtomUniverse := by
  decide

/-- 宇宙の要素はすべて表示用ベースに含まれる -/
theorem exactRowAtomUniverse_subset_basis :
    ∀ a ∈ exactRowAtomUniverse, a ∈ exactRowAtomBasis := by
  decide

/- 結論として、両者は集合として等しい (List.Perm を使う場合は追加の証明が必要ですが、要素の存在性はこれで十分) -/



/-- Coordinate vector of a target in the fixed display basis. -/
def exactRowCoordVectorOfTarget (tg : CoreKernelTarget) : List Bool :=
  exactRowAtomBasis.map (fun a => a ∈ rowAtomsOfTarget tg)

/-- Coordinate vector of a realized state in the fixed display basis. -/
def exactRowCoordVectorOfState (σ : CoreRealizedState) : List Bool :=
  exactRowAtomBasis.map (fun a => a ∈ rowAtomsOfState σ)

/-- Coarse 2-coordinate vector for the regime projection. -/
def regimeCoordVectorOfTarget (tg : CoreKernelTarget) : List Bool :=
  [ packageRegime tg = .pure
  , packageRegime tg = .bridgeSplit ]

theorem rowAtomsOfTarget_nfXASqAPred :
    rowAtomsOfTarget .nfXASqAPred =
      [ { slot := .sqAbsorb, channel := .right, tag := .nfXA }
      , { slot := .sqAbsorb, channel := .right, tag := .nfXASqRightPred } ] := by
  decide

theorem rowAtomsOfTarget_nfUSqLiftAPred :
    rowAtomsOfTarget .nfUSqLiftAPred =
      [ { slot := .sqAbsorb, channel := .left, tag := .nfU }
      , { slot := .sqAbsorb, channel := .left, tag := .nfUSqLiftRightPred } ] := by
  decide

theorem rowAtomsOfTarget_nfUDecorRightPred :
    rowAtomsOfTarget .nfUDecorRightPred =
      [ { slot := .sqAbsorb, channel := .left,  tag := .nfM }
      , { slot := .decor,    channel := .right, tag := .nfU } ] := by
  decide

end RowCoordinates

end Necessity
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
