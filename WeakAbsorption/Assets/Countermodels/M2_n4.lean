import WeakAbsorption.Spec.Signatures
--import WeakAbsorption.Tooling.ModelSearch.CounterexampleSearch

namespace WeakAbsorption
namespace Countermodels

open WeakAbsorption.Laws
/-
/-- n=4 で M2 の反例が見つかるか（再現チェック） -/
def m2Counterexample4? : Option (BinOp 4) :=
  ModelSearch.findCounterexample (n := 4) holdsM2B
-/
/-
#eval m2Counterexample4?.isSome
#eval match m2Counterexample4? with
  | some op => ModelSearch.opTable op
  | none => []
  -/

/-
探索で得た反例テーブル（row = x, col = y）:
[[0, 0, 0, 2],
 [0, 0, 0, 2],
 [0, 0, 2, 2],
 [0, 0, 2, 2]]
-/

/-- 探索で得た M2 反例を固定した演算（Fin 4 上） -/
def opM2_n4 : BinOp 4 := fun x y =>
  match x.1, y.1 with
  | 0, 0 => ⟨0, by decide⟩
  | 0, 1 => ⟨0, by decide⟩
  | 0, 2 => ⟨0, by decide⟩
  | 0, 3 => ⟨2, by decide⟩
  | 1, 0 => ⟨0, by decide⟩
  | 1, 1 => ⟨0, by decide⟩
  | 1, 2 => ⟨0, by decide⟩
  | 1, 3 => ⟨2, by decide⟩
  | 2, 0 => ⟨0, by decide⟩
  | 2, 1 => ⟨0, by decide⟩
  | 2, 2 => ⟨2, by decide⟩
  | 2, 3 => ⟨2, by decide⟩
  | 3, 0 => ⟨0, by decide⟩
  | 3, 1 => ⟨0, by decide⟩
  | 3, 2 => ⟨2, by decide⟩
  | 3, 3 => ⟨2, by decide⟩
  -- x,y : Fin 4 なので実際には到達しないが、match のために置く
  | _, _ => ⟨0, by decide⟩

/- 固定したテーブルが探索結果と一致するかの目視確認用 -/
--#eval ModelSearch.opTable opM2_n4

theorem opM2_n4_C1 : HoldsC1P opM2_n4 := by
  unfold HoldsC1P
  decide

theorem opM2_n4_C2p : HoldsC2pP opM2_n4 := by
  unfold HoldsC2pP
  decide

theorem opM2_n4_not_M2 : ¬ HoldsM2P opM2_n4 := by
  unfold HoldsM2P
  decide

/-- M2 が壊れる具体的な witness -/
theorem opM2_n4_m2_failure_witness :
    opM2_n4 (opM2_n4 (opM2_n4 0 0) 3) (opM2_n4 0 (opM2_n4 3 3))
      ≠ opM2_n4 (opM2_n4 0 0) 3 := by
  decide

end Countermodels
end WeakAbsorption
