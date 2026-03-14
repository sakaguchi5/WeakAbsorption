import WeakAbsorption.Classification.Phase1.Results

namespace WeakAbsorption
namespace Experiments

open WeakAbsorption.Classification.Phase1

/-
  ここは「配線の実行確認」専用。
  theorem / example は置かない（探索器を kernel reduction に背負わせない）。
-/

---#eval phase1Results4
---#eval phase1RefutedNames4
---#eval phase1SurvivedNames4

/-- 期待値スナップショット（軽い比較用） -/
def phase1RefutedNames4_expected : List String := ["M2"]
def phase1SurvivedNames4_expected : List String := ["C1", "C2'"]

---#eval (phase1RefutedNames4 == phase1RefutedNames4_expected)
---#eval (phase1SurvivedNames4 == phase1SurvivedNames4_expected)

/-
-- Lean の環境によっては #guard も使える（使えるならこちらの方が意図が明確）
#guard phase1RefutedNames4 = ["M2"]
#guard phase1SurvivedNames4 = ["C1", "C2'"]
-/

end Experiments
end WeakAbsorption
