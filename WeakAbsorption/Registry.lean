import WeakAbsorption.Classification.Shared.Defs
import WeakAbsorption.Classification.Shared.Status
import WeakAbsorption.Classification.Phase1.Certified

namespace WeakAbsorption
namespace Registry

open WeakAbsorption.Classification.Shared

/-!
## Registry statistics

`Stats` is a machine-readable summary of the current certified registry.
It is intentionally lightweight (no maps/finsets) to keep the core tooling simple.
-/

/-- Simple multiset-like counter as an association list. -/
private def bump {α : Type} [DecidableEq α] (a : α) : List (α × Nat) → List (α × Nat)
  | [] => [(a, 1)]
  | (b, n) :: xs =>
      if _h : a = b then
        (b, n + 1) :: xs
      else
        (b, n) :: bump a xs

/-- Counts by evidence constructor. -/
structure EvidenceTypeCounts where
  certifiedCountermodel : Nat
  searchCounterexample : Nat
  searchNoCounterexample : Nat
  certifiedTheorem : Nat
  deriving Repr

/-- Summary statistics for the certified registry. -/
structure Stats where
  total : Nat
  /-- Count by `CandidateStatus`. -/
  statusCounts : List (CandidateStatus × Nat)
  /-- Distribution of `n` for counterexample-like evidence. -/
  nCounts : List (Nat × Nat)
  /-- Distribution of theorem names used as certified evidence. -/
  thmCounts : List (Lean.Name × Nat)
  /-- Minimum `n` among *actual counterexamples* in the registry.

  This ignores "no counterexample up to n" evidence.
  -/
  minCounterexampleSize : Option Nat
  /-- The most frequently cited theorem name (with its count), if any. -/
  mostFrequentTheorem : Option (Lean.Name × Nat)
  /-- Counts by evidence constructor (machine-checkable provenance mix). -/
  evidenceTypeCounts : EvidenceTypeCounts
  deriving Repr

private def EvidenceTypeCounts.bump (c : EvidenceTypeCounts) : Evidence → EvidenceTypeCounts
  | .certifiedCountermodel _ _ _ => { c with certifiedCountermodel := c.certifiedCountermodel + 1 }
  | .searchCounterexample _      => { c with searchCounterexample := c.searchCounterexample + 1 }
  | .searchNoCounterexample _    => { c with searchNoCounterexample := c.searchNoCounterexample + 1 }
  | .certifiedTheorem _          => { c with certifiedTheorem := c.certifiedTheorem + 1 }

private def updateMin (m : Option Nat) (n : Nat) : Option Nat :=
  match m with
  | none => some n
  | some k => some (Nat.min k n)

private def maxCount {α : Type} : List (α × Nat) → Option (α × Nat)
  | [] => none
  | x :: xs =>
      some <| xs.foldl (fun best y => if y.2 > best.2 then y else best) x

/--
Single source of truth for **certified** classification results.

Policy:
- Only certified results live here.
- Pipeline/Experiments outputs do NOT belong here.
- This file is the only module whose name contains `Registry`.
-/
def registry : List ClassificationResult :=
  WeakAbsorption.Classification.Phase1.Certified.certifiedResults

/-- Lookup a classification result by candidate name. -/
def lookup (name : String) : Option ClassificationResult :=
  registry.find? (fun r => r.name = name)

/-- Unknown means "not in registry yet". -/
def isUnknown (name : String) : Bool :=
  (lookup name).isNone

/-- True iff the candidate is refuted in the registry. -/
def isRefuted (name : String) : Bool :=
  match lookup name with
  | some r => r.status == CandidateStatus.refuted
  | none   => false

/-- True iff the candidate survived (no counterexample in certified set). -/
def isSurvived (name : String) : Bool :=
  match lookup name with
  | some r => r.status == CandidateStatus.survived
  | none   => false

/-- All refuted entries (derived view). -/
def refuted : List ClassificationResult :=
  registry.filter (fun r => r.status == CandidateStatus.refuted)

/-- All survived entries (derived view). -/
def survived : List ClassificationResult :=
  registry.filter (fun r => r.status == CandidateStatus.survived)

/-- Compute a machine-readable summary of the current registry. -/
def stats : Stats :=
  let total := registry.length
  let statusCounts :=
    registry.foldl (fun acc r => bump r.status acc) []
  let nCounts :=
    registry.foldl
      (fun acc r =>
        match r.evidence with
        | .certifiedCountermodel n _ _ => bump n acc
        | .searchCounterexample n      => bump n acc
        | .searchNoCounterexample n    => bump n acc
        | .certifiedTheorem _          => acc)
      []
  let thmCounts :=
    registry.foldl
      (fun acc r =>
        match r.evidence with
        | .certifiedTheorem thm           => bump thm acc
        | .certifiedCountermodel _ _ thm  => bump thm acc
        | .searchCounterexample _         => acc
        | .searchNoCounterexample _       => acc)
      []
  let minCounterexampleSize :=
    registry.foldl
      (fun acc r =>
        match r.evidence with
        | .certifiedCountermodel n _ _ => updateMin acc n
        | .searchCounterexample n      => updateMin acc n
        | .searchNoCounterexample _    => acc
        | .certifiedTheorem _          => acc)
      none
  let evidenceTypeCounts :=
    registry.foldl (fun acc r => acc.bump r.evidence)
      { certifiedCountermodel := 0
        searchCounterexample := 0
        searchNoCounterexample := 0
        certifiedTheorem := 0 }
  let mostFrequentTheorem := maxCount thmCounts
  { total := total
    statusCounts := statusCounts
    nCounts := nCounts
    thmCounts := thmCounts
    minCounterexampleSize := minCounterexampleSize
    mostFrequentTheorem := mostFrequentTheorem
    evidenceTypeCounts := evidenceTypeCounts }

end Registry
end WeakAbsorption
