/-!
`Clean/` は `Necessity` フリーな clean-room 本体。

禁止事項:
- `WeakAbsorption.Proof.Generators.Vars1.Independence.Necessity.*` を直接 import しない。
- 旧 `Semantics/Instances/R4/R4KernelObservedSpec.lean` を直接 import しない。
- 旧 `PackageBridge.lean` を直接 import しない。

許される入力:
- `Semantics2/Core/*`
- `Semantics2/Targets/*`

要点:
- `Clean/` は「旧実装を読む層」ではなく、「再現目標を実装する層」。
-/
