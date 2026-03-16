import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Core.RowProfile

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Core

/--
Target-label sector for stage-1 Semantics3.

At this stage, the central object is the triple
`kernel / shell / state`.
`regime` is *not yet* removed from the main snapshot contract,
but R4 may show that it factors through this sector.
-/
structure ObservedTargetLabels where
  kernel : ObservedKernelClass
  shell : ObservedShellKind
  state : ObservedState
  deriving DecidableEq, Repr

/--
Row-geometry sector for stage-1 Semantics3.

At this stage, the central object is `rowProfile`.
`rowShape`, `atomCount`, and `shapeCount` are derived from it.
-/
structure ObservedRowGeometry where
  rowProfile : ObservedRowProfile
  deriving DecidableEq, Repr

namespace ObservedRowGeometry

def rowShape (g : ObservedRowGeometry) : List ObservedShapeCoord :=
  g.rowProfile.support

def atomCount (g : ObservedRowGeometry) : Nat :=
  g.rowProfile.atomCount

def shapeCount (g : ObservedRowGeometry) : Nat :=
  g.rowProfile.shapeCount

end ObservedRowGeometry

/--
Stage-1 snapshot contract.

Design:
- target-label sector:
  `labels`
- still-retained target-level coarse label:
  `regime`
- row-geometry sector:
  `geometry`
- still-retained coarse geometry quotient:
  `shapeFamily`

This is intentionally not yet minimal.
-/
structure ObservedKernelSnapshot where
  labels : ObservedTargetLabels
  regime : ObservedRegime
  geometry : ObservedRowGeometry
  shapeFamily : ObservedShapeFamily
  deriving DecidableEq, Repr

namespace ObservedKernelSnapshot

def kernel (s : ObservedKernelSnapshot) : ObservedKernelClass :=
  s.labels.kernel

def shell (s : ObservedKernelSnapshot) : ObservedShellKind :=
  s.labels.shell

def state (s : ObservedKernelSnapshot) : ObservedState :=
  s.labels.state

def rowProfile (s : ObservedKernelSnapshot) : ObservedRowProfile :=
  s.geometry.rowProfile

def rowShape (s : ObservedKernelSnapshot) : List ObservedShapeCoord :=
  s.geometry.rowShape

def atomCount (s : ObservedKernelSnapshot) : Nat :=
  s.geometry.atomCount

def shapeCount (s : ObservedKernelSnapshot) : Nat :=
  s.geometry.shapeCount

end ObservedKernelSnapshot

end Core
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
