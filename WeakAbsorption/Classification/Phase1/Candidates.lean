import WeakAbsorption.Spec.Signatures

namespace WeakAbsorption
namespace Classification
namespace Phase1

open WeakAbsorption.Laws

inductive CandidateKind where
  | axiomLike
  | mixed
  | unknown
deriving DecidableEq, Repr

/-- 探索で扱う候補（サイズ n 固定） -/
structure SearchCandidate (n : Nat) where
  name : String
  law  : LawB n
  kind : CandidateKind := .unknown



/-- Phase1 の最小候補集合（まずは配線確認用） -/
def phase1Candidates4 : List (SearchCandidate 4) :=
  [ { name := "C1",  law := holdsC1B,  kind := .axiomLike }
  , { name := "C2'", law := holdsC2pB, kind := .axiomLike }
  , { name := "M2",  law := holdsM2B,  kind := .mixed }
  ]

end Phase1
end Classification
end WeakAbsorption
