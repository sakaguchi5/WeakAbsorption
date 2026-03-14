import WeakAbsorption.Tooling.SmallCheck.Phase0
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

namespace WeakAbsorption.Experiments.Vars1

open WeakAbsorption
open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck
open WeakAbsorption.Proof.Generators.Vars1

/-- Fast manual probe for the first found gap under a chosen RuleSet. -/
def firstGap_tooling (K N : Nat) (R : RuleSet) : String :=
  let rec go (i : Nat) : String :=
    if _h : i < N then
      match findGapWithRedPathAfterNFGen K i R with
      | none => go (i+1)
      | some (u, v, _p) =>
          s!"FOUND GAP\nseed={i}\nR={repr R}\n" ++
          s!"u={termStr u}\nv={termStr v}\n"
    else
      s!"NO GAP FOUND\nR={repr R}\nK={K}, N={N}"
  go 0

-- Example interactive probe:
-- #eval firstGap_tooling 15 10 R4

end WeakAbsorption.Experiments.Vars1
