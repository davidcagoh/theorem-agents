# CLAUDE.md

This file provides repository-local guidance for agentic work in **theorem-agents**.

## Repository role

This repository is the **agentic theorem-proving layer** of the Lean portfolio. It formalizes four theorems characterizing the expected hitting time of policy-guided random traversal on AND-OR hypertrees — the theoretical foundation for neural theorem-proving complexity.

## Local authority rule

If shared handbook context is unavailable, treat this file and `README.md` as the authoritative operating guide for this repository.

## Shared ecosystem

This project is part of the **Stochastic Proofs Handbook** ecosystem. Use the handbook for shared Lean patterns and Aristotle workflow conventions, but use this file for repository-specific structure and cautions.

## Repository map

| Path | Role |
|---|---|
| `AutomatedProofs/AOTree/Defs.lean` | Core definitions and helper lemmas |
| `AutomatedProofs/AOTree/Theorem3.lean` | Zero-sum exploration theorem and policy-independent hardness |
| `AutomatedProofs/AOTree/Theorem1.lean` | Hitting time upper bound |
| `AutomatedProofs/AOTree/Theorem4.lean` | Sequential versus parallel search branch |
| `AutomatedProofs/AOTree/Theorem2.lean` | Monotone policy improvement and expert iteration soundness |
| `AutomatedProofs.lean` | Import entry point in dependency order |

## Commands

```bash
lake build
lake build AutomatedProofs.AOTree.Theorem3
python scripts/status.py
python scripts/submit.py my_theorems/lean4_andor_theorems_agent_spec.md "Fill in all the sorries" --dry-run
python scripts/submit.py my_theorems/lean4_andor_theorems_agent_spec.md "Fill in all the sorries"
python scripts/watch.py
python scripts/retrieve.py
```

## Project-specific cautions

| Area | Guidance |
|---|---|
| Import order | Update `AutomatedProofs.lean` carefully and preserve dependency order. |
| Local theorem scope | Keep proofs aligned with the current AND/OR tree formalization rather than generalizing prematurely. |
| Subtree reasoning | Be careful when a hypothesis about the root tree is incorrectly reused for subtrees. |
| Result merging | Aristotle jobs are snapshots; merge only proved changes rather than overwriting local files wholesale. |

## Submission policy

Prefer focused submissions for logically coherent theorem clusters. If one theorem depends on helper lemmas or local structural fixes, prove those first and keep the dependency chain explicit.

---

## Lean 4 Proof Patterns (confirmed for this project)

### Termination for recursive functions on `AOTree`

When recursing over a `List` of children, Lean cannot automatically prove termination. Use explicit membership binders:

```lean
def myFn : AOTree α → ...
  | orNode _ cs => ∃ (c : AOTree α) (_ : c ∈ cs), myFn c
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i hc
  have h := List.sizeOf_lt_of_mem hc
  omega
```

For index-based recursion (`cs.get i`), use `List.getElem_mem` to produce the membership proof:

```lean
termination_by t => sizeOf t
decreasing_by
  simp_wf
  have h := List.sizeOf_lt_of_mem (List.getElem_mem (by assumption))
  omega
```

### Key Mathlib lemma names

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

### Common pitfalls

- **`corollary` keyword**: Does not exist in Lean 4. Use `theorem` instead.
- **`Filter.tendsto_atTop_mono`**: Use the fully qualified name. `Filter.Tendsto.atTop_mono` does not exist. Use `exact Filter.tendsto_atTop_mono (fun n => ...) htend` directly — avoid `apply ... ?_` patterns.
- **Doc comment syntax errors**: If a syntax error points to the end of a `/-- ... -/` doc comment, the parser is misreading its content. Simplify the comment or use `--` line comments.
- **`hpmax` scoping**: When a hypothesis bounds `successProb π t nid` for the root tree `t`, it does not automatically bound subtrees. For the `andNode` case, children `cs.get i` are different trees. Either add a separate `hchildren` hypothesis or strengthen `hpmax` to quantify over all subtrees.
