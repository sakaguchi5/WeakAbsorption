# AGENTS.md

## Purpose

This repository is a Lean 4 project managed with Lake.
Work conservatively and prioritize keeping the proof graph understandable, scoped, and buildable.

## Working Style

- Read the relevant code first, explain the local structure briefly, and only then make changes.
- Keep changes scoped to the requested file(s) and the smallest reasonable set of direct dependencies.
- Prefer small, reviewable edits over broad rewrites.
- Preserve existing naming, file boundaries, and import layering unless there is a clear reason to change them.
- Avoid opportunistic cleanup outside the requested task.

## Ask First

Ask before doing any of the following:
- moving files across directories or layers
- introducing new cross-layer imports
- renaming theorems, definitions, files, or directories
- broad refactors or cleanup beyond the requested scope
- changing the main build surface or overall layer order
- editing multiple proof areas just to recover build health

## Repo-Specific Safety Rules

- Treat `WeakAbsorption.lean` as the main full-build entry for `lake build`.
- Respect the intended layer order as much as possible:
  Core -> Spec -> Proof -> Tooling -> Assets -> Classification -> Registry -> Experiments -> Examples
- Be careful not to blur the separation between older dependencies/results and clean-room reconstruction work.
- Avoid introducing new imports that unnecessarily mix foundational theorem files, tooling/search code, frozen assets, registry data, and experiments.
- If the requested task seems to require crossing these boundaries, explain why before proceeding.

## Proof Policy

- Prefer dependency analysis, structure cleanup, and import cleanup before attempting large proof synthesis.
- For large proof files, make the minimum local change needed.
- Preserve existing decomposition into steps/modules where possible.
- Avoid massive rewrites of proofs unless explicitly requested.
- Prefer adding a small local lemma over reshaping a large proof chain.

## Validation

- Default validation target: `lake build`.
- If a narrower validation target is obvious and cheaper, mention it.
- If build breakage appears outside the requested scope, report it clearly before widening the task.

## Output Expectations

- Summarize what changed, why it changed, and which files were touched.
- If the task is blocked by repo boundaries or missing context, say so explicitly.