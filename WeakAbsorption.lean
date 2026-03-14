/-
Architecture (entry point):
This file is intentionally "fat": it imports (directly) *all* modules in the repository so that
opening `WeakAbsorption.lean` lets you jump to any part of the codebase, and `lake build`
checks everything via this single entry.

Ordering rule of thumb:
Core → Spec → Proof → Tooling → Assets → Classification → Registry → Experiments → Examples
-/

-- =========================
-- Core (mathlib-free foundation)
-- =========================

import WeakAbsorption.Core.Syntax
import WeakAbsorption.Core.Rewrite
import WeakAbsorption.Core.Measure
import WeakAbsorption.Core.Termination
import WeakAbsorption.Core.Equational
import WeakAbsorption.Core.Algebra
import WeakAbsorption.Core.Quotient
import WeakAbsorption.Core.Semantics
import WeakAbsorption.Core.Free
import WeakAbsorption.Core.Universal
import WeakAbsorption.Core.Completeness
import WeakAbsorption.Core.Canonical
import WeakAbsorption.Core.Closure

-- =========================
-- Spec (shared currency)
-- =========================

import WeakAbsorption.Spec.Signatures
import WeakAbsorption.Spec.Rule
import WeakAbsorption.Spec.Equation

-- =========================
-- Proof layer
-- =========================

-- Transport
import WeakAbsorption.Proof.Transport.TypeEquiv
import WeakAbsorption.Proof.Transport.QuotRelTransport

-- Rewrite-facing lemmas
import WeakAbsorption.Proof.RewriteRoot

-- Generators (core framework)
import WeakAbsorption.Proof.Generators.NormalFormGenerators
import WeakAbsorption.Proof.Generators.Kernel
import WeakAbsorption.Proof.Generators.Builders
import WeakAbsorption.Proof.Generators.Sanity

-- Derived-rule facts
import WeakAbsorption.Proof.Generators.Derive.DoubleSqRedundant

-- Generators (orbit / K-dynamics / invariants / utilities)
import WeakAbsorption.Proof.Generators.Orbit.Basic
import WeakAbsorption.Proof.Generators.Orbit.KDynamics
import WeakAbsorption.Proof.Generators.Orbit.Families.SafeVarLeft
import WeakAbsorption.Proof.Generators.Orbit.Families.HoleLeftVar.Defs
import WeakAbsorption.Proof.Generators.Orbit.Families.HoleLeftVar.Witnesses
import WeakAbsorption.Proof.Generators.Orbit.Families.HoleLeftVar.Consequences
import WeakAbsorption.Proof.Generators.Orbit.Families.MixedCtx.Defs
import WeakAbsorption.Proof.Generators.Orbit.Families.MixedCtx.WitnessK11K13
import WeakAbsorption.Proof.Generators.Orbit.Invariants.LeafParitySafeCtxR
import WeakAbsorption.Proof.Generators.Orbit.Invariants.LeafParityCtxFlipAll
import WeakAbsorption.Proof.Generators.Utils.StripLite

-- Vars=1 shared names / rule sets
import WeakAbsorption.Proof.Generators.Vars1.RuleSets

-- Vars=1 completeness pipeline
import WeakAbsorption.Proof.Generators.Vars1.Complete.Main

-- Vars=1 generator independence / necessity
import WeakAbsorption.Proof.Generators.Vars1.Independence.Main

-- Vars=1 semantic-system façade
import WeakAbsorption.Proof.Generators.Vars1.Independence.Semantics.Main

-- Necessity / legacy / rechecks
import WeakAbsorption.Proof.Generators.Necessity.K11
import WeakAbsorption.Proof.Generators.SqStableRecheck

-- Counterexample / non-confluence / kernel-collapse cluster
import WeakAbsorption.Proof.Counterexample.DistinctNormals
import WeakAbsorption.Proof.Counterexample.LocalConfluence
import WeakAbsorption.Proof.Counterexample.KernelCollapse

-- =========================
-- Tooling layer
-- =========================

import WeakAbsorption.Tooling.ModelSearch.Core
import WeakAbsorption.Tooling.ModelSearch.CounterexampleSearch
import WeakAbsorption.Tooling.Probe
import WeakAbsorption.Tooling.ProbeEval
import WeakAbsorption.Tooling.SmallCheck.Phase0

-- =========================
-- Assets (frozen results)
-- =========================

import WeakAbsorption.Assets.Countermodels.M2_n4
import WeakAbsorption.Assets.Countermodels.Certified

-- =========================
-- Classification / Registry
-- =========================

import WeakAbsorption.Classification.Shared.Status
import WeakAbsorption.Classification.Shared.Defs
import WeakAbsorption.Registry
import WeakAbsorption.Classification.Phase1.Candidates
import WeakAbsorption.Classification.Phase1.Pipeline
import WeakAbsorption.Classification.Phase1.Results
import WeakAbsorption.Classification.Phase1.Certified

-- =========================
-- Experiments (debug / snapshots)
-- =========================

import WeakAbsorption.Experiments.Snapshot
import WeakAbsorption.Experiments.SmallCheckK11Snapshot
import WeakAbsorption.Experiments.TermStrCheck
import WeakAbsorption.Experiments.Phase1Smoke

-- Vars=1 exploration
import WeakAbsorption.Experiments.Vars1.SearchR4

-- =========================
-- Examples
-- =========================

import WeakAbsorption.Examples.Basic
