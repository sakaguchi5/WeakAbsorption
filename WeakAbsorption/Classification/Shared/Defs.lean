import WeakAbsorption.Classification.Shared.Status

namespace WeakAbsorption.Classification.Shared

open CandidateStatus
open Lean
/--
Machine-readable evidence for a classification decision.

Design intent:
- `Evidence` is the *source of truth*.
- Human-facing explanations (if any) belong in `ClassificationResult.note`.
- Certified results should point to a theorem name (and, when applicable, a concrete countermodel witness).
- Search results should record the searched size `n`.
- We keep this minimal and extensible (add constructors as the project grows).
-/
inductive Evidence where
  | certifiedTheorem (thm : Name)
  | certifiedCountermodel (n : Nat) (witness : Name) (thm : Name)
  | searchCounterexample (n : Nat)
  | searchNoCounterexample (n : Nat)

instance : Repr Evidence where
  reprPrec e _ :=
    match e with
    | .certifiedTheorem thm =>
        s!"Evidence.certifiedTheorem({toString thm})"
    | .certifiedCountermodel n wit thm =>
        s!"Evidence.certifiedCountermodel(n := {n}, witness := {toString wit}, thm := {toString thm})"
    | .searchCounterexample n =>
        s!"Evidence.searchCounterexample(n := {n})"
    | .searchNoCounterexample n =>
        s!"Evidence.searchNoCounterexample(n := {n})"

/-- 分類結果の構造 -/
structure ClassificationResult where
  name : String
  status : CandidateStatus
  evidence : Evidence
  note   : Option String := none
  deriving Repr

end WeakAbsorption.Classification.Shared
