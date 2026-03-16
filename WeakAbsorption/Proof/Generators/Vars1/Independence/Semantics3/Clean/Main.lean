import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Core.Main
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics3.Targets.Main

namespace WeakAbsorption
namespace Proof
namespace Generators
namespace Vars1
namespace Independence
namespace Semantics3
namespace Clean

open Core
open Targets

/--
Stage-1 clean entry point.

At this stage, clean reconstruction is not yet implemented.
What *is* fixed here is the public snapshot language and the audited R4 snapshot source.
-/
abbrev SnapshotSource := ObservedTarget -> ObservedKernelSnapshot

def r4SnapshotSource : SnapshotSource :=
  observedSnapshot

end Clean
end Semantics3
end Independence
end Vars1
end Generators
end Proof
end WeakAbsorption
