import WeakAbsorption.Spec.Signatures
import WeakAbsorption.Tooling.ModelSearch.CounterexampleSearch
import WeakAbsorption.Classification.Shared.Status
import WeakAbsorption.Classification.Shared.Defs

namespace WeakAbsorption
namespace Classification
namespace Phase1

open WeakAbsorption.Laws
open WeakAbsorption.Classification.Shared

/-- 指定サイズ n で候補 law を反例探索し、最小の分類結果を返す -/
def classifyBySearch (n : Nat) (nm : String) (law : LawB n) : ClassificationResult :=
  match ModelSearch.findCounterexample (n := n) law with
  | some _ =>
      { name := nm
        status := CandidateStatus.refuted
        evidence := Evidence.searchCounterexample n
        note := some (s!"counterexample found on Fin {n}") }
  | none =>
      { name := nm
        status := CandidateStatus.survived
        evidence := Evidence.searchNoCounterexample n
        note := some (s!"no counterexample found on Fin {n}") }

/-- M2 を n=4 で試す最初の配線確認 -/
def classifyM2_n4 : ClassificationResult :=
  classifyBySearch 4 "M2" holdsM2B

--#eval classifyM2_n4

end Phase1
end Classification
end WeakAbsorption
