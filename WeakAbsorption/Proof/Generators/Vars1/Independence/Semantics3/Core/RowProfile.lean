import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Core.Labels

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Core

structure ObservedShapeCoord where
  kind : ObservedRuleKind
  side : ObservedSide
  deriving DecidableEq, Repr

/--
Multiplicity-aware row profile.

Interpretation:
- `counts = [(c₁, n₁), ..., (cₖ, nₖ)]`
  means that the coarse coordinate `cᵢ` appears `nᵢ` times.
- We keep this as a simple finite list for now.
- Normalization / invariants can be added later.
-/
structure ObservedRowProfile where
  counts : List (ObservedShapeCoord × Nat)
  deriving DecidableEq, Repr

namespace ObservedShapeCoord

def mkCoord (kind : ObservedRuleKind) (side : ObservedSide) : ObservedShapeCoord :=
  { kind := kind, side := side }

end ObservedShapeCoord

namespace ObservedRowProfile

def empty : ObservedRowProfile :=
  { counts := [] }

def singleton (kind : ObservedRuleKind) (side : ObservedSide) : ObservedRowProfile :=
  { counts := [(ObservedShapeCoord.mkCoord kind side, 1)] }

def ofCounts (xs : List (ObservedShapeCoord × Nat)) : ObservedRowProfile :=
  { counts := xs }

def support (p : ObservedRowProfile) : List ObservedShapeCoord :=
  p.counts.map Prod.fst

def atomCount (p : ObservedRowProfile) : Nat :=
  p.counts.foldl (fun acc e => acc + e.snd) 0

def shapeCount (p : ObservedRowProfile) : Nat :=
  p.counts.length

end ObservedRowProfile

end Core
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
