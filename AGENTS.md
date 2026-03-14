# AGENTS.md

## Purpose

This repository is a Lean 4 project managed with Lake.

The highest-priority constraint in this repository is theoretical independence.
Do not trade away independence for convenience.

Work conservatively and prioritize keeping the proof graph understandable, scoped, buildable, and theory-internal.

## Repository Shape

Treat the repository structure as intentional, not incidental.

Primary build entry:
- `WeakAbsorption.lean`

Main repository areas under `WeakAbsorption/`:
- `Core`
- `Spec`
- `Proof`
- `Tooling`
- `Assets`
- `Classification`
- `Registry.lean`
- `Experiments`
- `Examples`

Important convention:
- `Registry` is currently a single file (`Registry.lean`), not a directory.
- `Assets/Countermodels` is part of the frozen/reference side of the repo and should be handled conservatively.

## Global Priorities

When in doubt, optimize for the following, in this order:
1. independence of the theory
2. correctness of boundaries and imports
3. minimal local change
4. proof clarity
5. buildability
6. convenience

Do not optimize for short-term proof speed by weakening the architectural boundaries.

## Independence Policy

- `Mathlib` is completely forbidden in this repository.
- Do not import `Mathlib` anywhere in this repository.
- Do not add wrappers, helper modules, re-exports, or transitive dependencies that pull in `Mathlib`.
- Do not solve proof gaps by importing external machinery that is not already part of this repository's current Lean/Lake environment.
- Preserve the theory as self-contained within this repository.
- If a result seems to require machinery that would usually come from `Mathlib`, stop and identify the missing local abstraction, local lemma, or local structural refactor instead.
- Never justify a `Mathlib` import by convenience, automation, proof length, or familiarity.

## Working Style

- Read the relevant files first and explain the local dependency structure briefly before editing.
- Keep changes scoped to the requested file(s) and the smallest reasonable set of direct dependencies.
- Prefer small, reviewable edits over broad rewrites.
- Preserve existing theorem names, file boundaries, and import layering unless there is a clear reason to change them.
- Avoid opportunistic cleanup outside the requested task.
- Prefer explicit local lemmas over broad proof rewrites.
- Preserve existing decomposition into smaller proof steps/modules when possible.
- Do not silently “improve” architecture while solving an unrelated local proof issue.

## Layer Discipline

Respect the intended repository flow as much as possible:

- `Core` -> foundational syntax/data/basic infrastructure
- `Spec` -> rule/specification layer
- `Proof` -> mathematical/proof development over core/spec
- `Tooling` -> search/check/enumeration/support code, not foundational theory
- `Assets` -> frozen/reference artifacts, countermodels, supporting fixed data
- `Classification` -> classification-facing results built on the stable lower layers
- `Registry.lean` -> registry/view/aggregation surface
- `Experiments` -> exploratory work, not a place to define foundational dependencies
- `Examples` -> usage/demo surface, not a place to host core theory

Operational rules:
- Do not move definitions downward in the dependency graph unless explicitly requested.
- Do not make foundational theory depend on `Tooling`, `Experiments`, or `Examples`.
- Do not use `Examples` as a hidden proof-support layer.
- Do not let `Experiments` become an undeclared dependency for stable theory.
- Do not treat `Assets` as a dumping ground for active proof code.
- Keep `Classification` and `Registry.lean` dependent on stable lower layers rather than ad hoc local hacks.

## Clean-Room / Legacy Boundary Rules

This repository contains a meaningful distinction between clean-room reconstruction work and older dependency-based or previously established material.
Do not blur that distinction.

- Preserve the separation between old-result reuse and clean-room reconstruction.
- If a file is intended to be clean-room, keep it free from old dependency shortcuts.
- If a file is intended to be observed/frozen/bridge-like, keep that role narrow.
- Do not turn boundary files into general-purpose import hubs.
- Derived/reconstruction-facing files should depend on stable observed interfaces, not directly on older proof artifacts.
- If a task seems to require crossing this boundary, stop and explain the exact pressure point instead of silently crossing it.

## Area-Specific Rules

### Core
- Keep `Core` small, stable, and foundational.
- Do not import higher-level classification, experimental, or example material into `Core`.
- Do not bury proof-specific hacks into foundational definitions.

### Spec
- Keep `Spec` close to the formal rule layer.
- Avoid mixing specification with exploratory search/tooling code.

### Proof
- Prefer local lemma extraction over global reshaping.
- Keep proofs aligned with the existing structural decomposition.
- Do not import experimental code just to close proof gaps.

### Tooling
- Treat `Tooling` as support code, not as a source of mathematical truth.
- Do not let search/enumeration utilities dictate the architecture of the proof layer.
- Do not move foundational definitions into `Tooling`.

### Assets
- Treat `Assets` as conservative, reference-like material.
- In particular, handle `Assets/Countermodels` as frozen/supporting content unless explicitly asked to redesign it.
- Do not casually rewrite or repurpose assets to patch theory-layer problems.

### Classification
- Keep classification results downstream from stable theory.
- Do not push unstable experiments into classification-facing results.

### Registry.lean
- Treat `Registry.lean` as an aggregation/view surface.
- Do not overload it with foundational definitions or exploratory proofs.
- Prefer feeding it stable results from lower layers.

### Experiments
- Keep experiments isolated.
- Do not promote experimental shortcuts into stable theory without explicit approval.
- Do not use experiments as hidden infrastructure for the rest of the repository.

### Examples
- Keep examples illustrative and non-foundational.
- Do not hide essential lemmas or architecture-critical code in examples.

## Ask First

Ask before doing any of the following:
- moving files across directories or layers
- splitting or merging major files
- introducing new cross-layer imports
- renaming theorems, definitions, files, or directories
- broad refactors or cleanup beyond the requested scope
- changing the main build surface
- changing clean-room / legacy / bridge boundaries
- rewriting registry/classification flow
- editing multiple proof areas just to recover build health
- changing whether material belongs in `Assets`, `Classification`, `Registry.lean`, `Experiments`, or `Examples`
- introducing any new external dependency for proof convenience

## Proof Policy

- Prefer dependency analysis, structure cleanup, and import cleanup before attempting large proof synthesis.
- For large proof files, make the minimum local change needed.
- Preserve existing decomposition into steps/modules where possible.
- Avoid massive rewrites of proofs unless explicitly requested.
- Prefer adding a small local lemma over reshaping a large proof chain.
- Prefer explicit local reasoning over opaque automation.
- Prefer repo-internal lemmas and structures over new abstractions with wide blast radius.
- When blocked, identify the exact missing intermediate statement instead of compensating with a broader rewrite.
- Do not “solve” a boundary problem by importing from a convenient but architecturally wrong location.

## Validation

Default validation target:
- `lake build`

Validation rules:
- If a narrower target is obvious and cheaper, mention it explicitly.
- If you only checked a narrower target, say so clearly.
- If build breakage appears outside the requested scope, report it before widening the task.
- Do not claim success without stating what was actually checked.
- Do not treat “the proof term compiles” as enough if layer boundaries or independence constraints were violated.

## Output Expectations

Always report:
- what changed
- why it changed
- which files were touched
- which imports changed, if any
- what was validated

Also report:
- any boundary assumptions
- any unresolved dependency pressure
- any place where the requested direction would violate independence or architectural boundaries

If blocked, say exactly what the blocking point is.
Do not hide architectural damage behind a successful local proof.