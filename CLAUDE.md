# CLAUDE.md

This file provides guidance to Claude Code when working with the `theorem-agents` repository.

The parent `../CLAUDE.md` covers shared workflow, Lean conventions, Mathlib API patterns, and Aristotle submission guidelines. This file covers project-specific details.

## High-Level Architecture

This repository contains multiple Lean 4 formalization tracks, primarily focused on automated theorem proving using Aristotle.

### 1. AND-OR Hypertree Hitting-Time Theorems (In Progress)
Formalizes four theorems about stochastic proof search on AND-OR hypertrees. The recommended implementation order is Theorem 3 → 1 → 4 → 2.
*   **`AOTree/Defs.lean`**: The core shared infrastructure. Defines the `AOTree` inductive type, `successProb` (using `NNReal`), and OR-node policies. Contains crucial cross-theorem helper lemmas (`sum_prod_erase_le_one`, `NNReal.weighted_sum_mono`) that must be completed to support downstream theorems.
*   **`AOTree/Theorem3.lean`**: The simplest theorem and recommended starting point. Establishes that AND-branching imposes policy-independent hardness.
*   **`AOTree/Theorem1.lean`**: Proves the hitting time upper bound.
*   **`AOTree/Theorem4.lean`**: An algebraic branch comparing sequential vs. parallel search. Mostly self-contained combinatorial proofs.
*   **`AOTree/Theorem2.lean`**: The most advanced theorem. Formalizes monotone policy improvement and expert iteration soundness. Heavily relies on the helper lemmas from `Defs.lean`.

### 2. JEPA Learning Dynamics Proof (Complete)
Proves that a depth-L ≥ 2 linear JEPA model learns features in decreasing order of their generalized regression coefficient.
*   **`JEPA.lean`**: The main proof file.
*   **`Lemmas.lean`**: Substantial classical helper results not in Mathlib (e.g., positive-definite quadratic/Frobenius lower bounds).
*   **`OffDiagHelpers.lean`**: Bridging lemmas that adapt general results from `Lemmas.lean` into the exact inequalities needed by `JEPA.lean`.

### 3. Standalone Classical Analysis
*   **`GronwallIntegral.lean`**: A self-contained formalization of the variable-coefficient integral form of Grönwall's inequality, using an integrating-factor argument.

**Entry Point**: `AutomatedProofs.lean` imports all files in strict dependency order. When adding a new theorem file, insert its import here **after** any files it depends on.

## Development Workflow & Commands

The general workflow is: write a proof paper (markdown) → translate it into a Lean skeleton with `sorry` placeholders and `PROVIDED SOLUTION` docstrings → submit to Aristotle → retrieve filled proofs.

### Building and Testing
*   **Build entire project**: `lake build`
*   **Build/test a single file**: `lake build AutomatedProofs.AOTree.Theorem3` (This elaborates only the specified module and its dependencies, effectively running the "tests" for that file).

### Aristotle Submission Loop
Scripts are located in `scripts/` and should be run from the project root.
*   **Check progress**: `python scripts/status.py`
    *   Scans Lean files for remaining `sorry`s (ignoring comments/docstrings) and shows in-flight Aristotle jobs.
*   **Submit to Aristotle**: `python scripts/submit.py my_theorems/lean4_andor_theorems_agent_spec.md "Fill in all the sorries"`
    *   Use `--dry-run` to preview the packaged files.
    *   The paper path is required to link the submission to its source.
*   **Watch jobs**: `python scripts/watch.py`
    *   Adaptively polls in-flight jobs and **auto-runs retrieval** when jobs complete.
*   **Retrieve manually**: `python scripts/retrieve.py`
    *   Downloads completed jobs and annotates the corresponding markdown papers in `reports/`.

### Scaffolding New Theorems
Use the custom Claude skill to scaffold a Lean skeleton from a markdown paper:
```bash
/new-theorem my_theorems/Paper.md
```
This skill reads `lakefile.toml` for the module name, infers the theorem name, identifies lemmas, writes skeleton files with `PROVIDED SOLUTION` docstrings, updates `AutomatedProofs.lean`, and runs a dry-run before offering to submit.

## Environment Notes
*   **Mathlib Cache**: The repository is designed to be cloned inside a dedicated parent folder (e.g., `~/lean-projects/`) so that the ~7.7 GB Mathlib cache in `.lean-packages/` can be shared across multiple projects.
*   **Toolchain**: Pinned to `leanprover/lean4:v4.28.0` and Mathlib `v4.28.0` to match Aristotle's fixed environment.
