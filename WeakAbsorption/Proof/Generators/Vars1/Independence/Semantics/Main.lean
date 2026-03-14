import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Core.Main
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Instances.Main
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Comparisons.Main

/-!
Semantic-system façade for Vars1 independence work.

This layer is meant to become the future-facing API:
- `Core/` defines the rule-relative semantic-system interface,
- `Instances/` houses concrete systems such as the current audited `R4`,
- `Comparisons/` reserves the comparison layer for future `R`-to-`R` studies.
-
The existing `Necessity/` tree remains the proof forest / construction archive.
This `Semantics/` tree is the reorganized semantic surface.
-/
