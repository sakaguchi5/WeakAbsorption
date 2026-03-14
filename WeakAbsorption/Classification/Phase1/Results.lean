import WeakAbsorption.Classification.Shared.Status
import WeakAbsorption.Classification.Phase1.Pipeline
import WeakAbsorption.Classification.Phase1.Candidates

namespace WeakAbsorption
namespace Classification
namespace Phase1

open WeakAbsorption.Classification.Shared

/-- 候補一覧を探索で分類する（最小版） -/
def runCandidates {n : Nat} (xs : List (SearchCandidate n)) : List ClassificationResult :=
  xs.map (fun c => classifyBySearch n c.name c.law)

/-- Phase1 最小結果（n=4） -/
def phase1Results4 : List ClassificationResult :=
  runCandidates phase1Candidates4
--#eval phase1Results4

/- 見やすい表示（名前と状態だけ） -/
--#eval phase1Results4.map (fun r => (r.name, r.status))

/-- 指定状態の候補名を抜き出す -/
def namesWithStatus (st : CandidateStatus) (xs : List ClassificationResult) : List String :=
  (xs.filter (fun r => r.status = st)).map (fun r => r.name)

def phase1RefutedNames4 : List String :=
  namesWithStatus CandidateStatus.refuted phase1Results4

def phase1SurvivedNames4 : List String :=
  namesWithStatus CandidateStatus.survived phase1Results4

end Phase1
end Classification
end WeakAbsorption
