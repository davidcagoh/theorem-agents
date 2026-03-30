# CLAUDE.md

This file provides guidance to Claude Code when working with the `theorem-agents` repository.

The parent `../CLAUDE.md` covers shared workflow, Lean conventions, Mathlib API patterns, and Aristotle submission guidelines. This file covers project-specific details.

## High-Level Architecture

This repository is dedicated to formalizing theorems about stochastic proof search on AND-OR hypertrees in Lean 4, primarily focused on automated theorem proving using Aristotle.

### AND-OR Hypertree Hitting-Time Theorems (In Progress)
Formalizes four theorems characterizing the expected hitting time of a policy-guided random traversal. The recommended implementation order is Theorem 3 → 1 → 4 → 2.
*   **`AOTree/Defs.lean`**: The core shared infrastructure. Defines the `AOTree` inductive type, `successProb` (using `NNReal`), and OR-node policies. Contains crucial cross-theorem helper lemmas (`sum_prod_erase_le_one`, `NNReal.weighted_sum_mono`) that must be completed to support downstream theorems.
*   **`AOTree/Theorem3.lean`**: The simplest theorem and recommended starting point. Establishes that AND-branching imposes policy-independent hardness.
*   **`AOTree/Theorem1.lean`**: Proves the hitting time upper bound.
*   **`AOTree/Theorem4.lean`**: An algebraic branch comparing sequential vs. parallel search. Mostly self-contained combinatorial proofs.
*   **`AOTree/Theorem2.lean`**: The most advanced theorem. Formalizes monotone policy improvement and expert iteration soundness. Heavily relies on the helper lemmas from `Defs.lean`.

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

## Lean 4 Proof Patterns (Confirmed Working in v4.28.0)

### Termination for Recursive Functions on Nested Inductives

When recursing over a `List` of children (e.g., `AOTree`), Lean cannot automatically prove termination. Use explicit membership binders so the proof is available to `omega`:

```lean
-- Use explicit membership: ∃ (c : AOTree α) (hc : c ∈ cs), ...
-- NOT implicit:           ∃ c ∈ cs, ...
def myFn : AOTree α → ...
  | orNode _ cs => ∃ (c : AOTree α) (_ : c ∈ cs), myFn c
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i hc
  have h := List.sizeOf_lt_of_mem hc
  omega
```

For index-based recursion (`cs.get i` or `cs[i]`), use `List.getElem_mem` to produce the membership proof:

```lean
termination_by t => sizeOf t
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem (List.getElem_mem (by assumption))
  omega
```

### Key Mathlib Lemma Names

| Goal | Lemma |
|------|-------|
| `1 - ε ≤ 1` | `tsub_le_self` |
| `0 < 1 - ε` from `ε < 1` | `tsub_pos_of_lt` |
| `1 - ε < 1` | `tsub_lt_self one_pos hε` |
| `b⁻¹ ≤ a⁻¹` from `a ≤ b` | `inv_anti₀ hpos hle` |
| `(a⁻¹)^n = (a^n)⁻¹` | `inv_pow` |
| `1 < a/b` iff `b < a` | `one_lt_div₀ hb_pos` |
| `a^n ≤ a^m` when `a ≤ 1, m ≤ n` | `pow_le_pow_of_le_one` |
| `r^n → ∞` when `1 < r` | `tendsto_pow_atTop_atTop_of_one_lt` |
| `g → ∞` from `f ≤ g` and `f → ∞` | `Filter.tendsto_atTop_mono` (fully qualified) |
| `0 ≤ 1` in `mul_le_mul_of_nonneg_left` | use `zero_le_one`, not `le_rfl` |

### Common Pitfalls

- **`corollary` keyword**: Does not exist in Lean 4. Use `theorem` instead.
- **`Filter.tendsto_atTop_mono`**: Use the fully qualified name. `Filter.Tendsto.atTop_mono` does not exist. Also avoid `apply ... ?_` patterns — use `exact Filter.tendsto_atTop_mono (fun n => ...) htend` directly.
- **Doc comment syntax errors**: If a syntax error points to the end of a `/-- ... -/` doc comment, the parser is misreading its content. Simplify the comment or use `--` line comments.
- **`hpmax` scoping**: When a hypothesis bounds `successProb π t nid` for the root tree `t`, it does not automatically bound subtrees. For the `andNode` case, children `cs.get i` are different trees. Either add a separate `hchildren` hypothesis or strengthen `hpmax` to quantify over all subtrees.

## Environment Notes
*   **Mathlib Cache**: The repository is designed to be cloned inside a dedicated parent folder (e.g., `~/lean-projects/`) so that the ~7.7 GB Mathlib cache in `.lean-packages/` can be shared across multiple projects.
*   **Toolchain**: Pinned to `leanprover/lean4:v4.28.0` and Mathlib `v4.28.0` to match Aristotle's fixed environment.
