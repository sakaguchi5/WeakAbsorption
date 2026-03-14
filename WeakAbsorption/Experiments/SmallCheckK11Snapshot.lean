import WeakAbsorption.Tooling.SmallCheck.Phase0
import WeakAbsorption.Spec.Rule

namespace WeakAbsorption
namespace Experiments
namespace SmallCheckK11Snapshot

open WeakAbsorption.Spec
open WeakAbsorption.SmallCheck

/-!
# SmallCheck K=11 Snapshot (NFGen)

Purpose:
- Freeze the current "discovery order" (必要性の順序) at K=11.
- Keep this as an *experiment/snapshot* file (do not import from Core/Proof).
- If this ever changes, it signals a behavioral change in SmallCheck or generator definitions.

What we record (K=11):
- R = []                       : gap exists
- R = [SqAbsorb]               : gap exists
- R = [SqAbsorb, SqStable]     : no gap
- Canonicalized core signatures (AllUnique) at each stage
- Orbit check for two representative cores (s~Au and A~Au)
-/

-- ---- Common parameters ----

/-- strip function used in the conversation: depth = 1. -/
def strip1 (u v : Term V) :=
  stripCommonCtxDepth (α := V) 1 u v

/-- The three staged RuleSets at K=11. -/
def R0 : RuleSet := []
def R1 : RuleSet := [RuleId.SqAbsorb]
def R2 : RuleSet := [RuleId.SqAbsorb, RuleId.SqStable]

/-- Universe bound for this snapshot. -/
def K : Nat := 11

/-- How many (unique) core signatures to collect (kept modest). -/
def howMany : Nat := 50

-- ---- Snapshot: core signatures (canonical + unique) ----

/-- Canonical + unique core signatures at K=11, R=[] -/
def sigs_R0 : List String :=
  collectCoreSigsNFGenAllUnique K howMany (R := R0)

/-- Canonical + unique core signatures at K=11, R=[SqAbsorb] -/
def sigs_R1 : List String :=
  collectCoreSigsNFGenAllUnique K howMany (R := R1)

/-- Canonical + unique core signatures at K=11, R=[SqAbsorb,SqStable] -/
def sigs_R2 : List String :=
  collectCoreSigsNFGenAllUnique K howMany (R := R2)

-- ---- Snapshot: existence of a gap ----

/-- True iff a gap exists at K=11 for rule set R. -/
def hasGap (R : RuleSet) : Bool :=
  match findGapWithRedPathNFGen K (R := R) with
  | none => false
  | some _ => true

def gap_R0 : Bool := hasGap R0
def gap_R1 : Bool := hasGap R1
def gap_R2 : Bool := hasGap R2

-- ---- Representative orbit checks (conversation's two cores) ----

-- Terms over vars=1
def x : Term V := Term.var 0
def s : Term V := x ⋆ x
def A : Term V := s ⋆ s
def Au : Term V := A ⋆ x

/-- Orbit contexts making (s,Au) a NFGen gap under R=[SqAbsorb], bounded by K=11. -/
def orbit_s_Au : List String :=
  orbitGapContextsNFGen
    K
    5  -- Kbase (fillers size bound)
    2  -- depth
    R1
    s Au

/-- Orbit contexts making (A,Au) a NFGen gap under R=[SqAbsorb], bounded by K=11. -/
def orbit_A_Au : List String :=
  orbitGapContextsNFGen
    K
    5
    2
    R1
    A Au

-- ---- Printouts (kept as #eval, since this is an experiment file) ----

/-負荷を避けるために基本はコメントアウト
#eval sigs_R0
#eval sigs_R1
#eval sigs_R2

#eval gap_R0
#eval gap_R1
#eval gap_R2

#eval orbit_s_Au
#eval orbit_A_Au
-/

/-!
Expected (based on the current state in the conversation):

sigs_R0 =
  ["ctx=□ | core=(((x⋆x)⋆(x⋆x)) , (x⋆x))",
   "ctx=(x⋆□) | core=(((x⋆x)⋆(x⋆x)) , (x⋆x))",
   "ctx=(□⋆x) | core=(((x⋆x)⋆(x⋆x)) , x)",
   "ctx=□ | core=((((x⋆x)⋆(x⋆x))⋆x) , ((x⋆x)⋆(x⋆x)))"]

sigs_R1 =
  ["ctx=(□⋆x) | core=(((x⋆x)⋆(x⋆x)) , x)",
   "ctx=□ | core=((((x⋆x)⋆(x⋆x))⋆x) , ((x⋆x)⋆(x⋆x)))"]

sigs_R2 = []

gap_R0 = true
gap_R1 = true
gap_R2 = false

orbit_s_Au =
  ["ctx=□ | u=(x⋆x) | v=(((x⋆x)⋆(x⋆x))⋆x)"]

orbit_A_Au =
  ["ctx=□ | u=((x⋆x)⋆(x⋆x)) | v=(((x⋆x)⋆(x⋆x))⋆x)"]
-/

end SmallCheckK11Snapshot
end Experiments
end WeakAbsorption
