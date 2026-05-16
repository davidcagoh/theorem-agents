# stochastic-search-bounds

Lean 4 formalization of hitting-time theorems for policy-guided AND/OR hypertree search — the theoretical foundation for the complexity of neural theorem-proving. Part of the [lean-workspace](https://github.com/davidcagoh/lean-workspace) methodology workspace.

## Results

Four theorems on AND/OR tree search under a stochastic policy:

1. **Theorem 1 — hitting-time upper bound.** A policy that puts at least probability $p$ on every successful child reaches the target within an expected number of expansions that scales polynomially with depth.
2. **Theorem 2 — monotone policy improvement.** Under a locality-respecting weakening of "puts more mass on correct children" (`hcorrect_better`), success probability is monotone in the policy. The clean form of the hypothesis is the contribution; the original formulation is too strong.
3. **Theorem 3 — zero-sum / policy-independent hardness.** A lower bound that holds against *any* policy, not just a fixed one.
4. **Theorem 4 — sequential vs. parallel search.** A sharp version of the inequality $\sum q(i) \le 1$ (replacing the loose $q(i) \le 1/2$ regime).

Together these characterize when policy-guided search has polynomial expected runtime and when it provably does not — directly relevant to the question of when LLM-driven theorem-proving can be tractable.

**Status.** 18pp paper at `my_theorems/paper.tex`, compiles clean. **Lean formalization has 0 sorries.** `lake build` runs to completion. This is the workspace's strongest validation case: every load-bearing claim in the paper is formally verified.

## Repository structure

| Path | Role |
|---|---|
| `AutomatedProofs/AOTree/Defs.lean` | Core definitions and helper lemmas |
| `AutomatedProofs/AOTree/Theorem1.lean` | Hitting time upper bound |
| `AutomatedProofs/AOTree/Theorem2.lean` | Monotone policy improvement |
| `AutomatedProofs/AOTree/Theorem3.lean` | Zero-sum exploration / policy-independent hardness |
| `AutomatedProofs/AOTree/Theorem4.lean` | Sequential vs parallel search |
| `my_theorems/paper.tex` | LaTeX paper (18pp) |
| `my_theorems/lean4_andor_theorems_agent_spec.md` | Theorem spec submitted to Aristotle |
| `requests/` | Aristotle submission prompts |
| `results/` | Aristotle result tarballs |

## Commands

```bash
lake build
lake build AutomatedProofs.AOTree.Theorem3

python ../stochastic-proofs-handbook/scripts/status.py
python ../stochastic-proofs-handbook/scripts/submit.py my_theorems/lean4_andor_theorems_agent_spec.md "Fill in the sorries"
python ../stochastic-proofs-handbook/scripts/retrieve.py [project-id]
```

## Setup

```bash
pip install aristotlelib pathspec python-dotenv
# API key in lean-workspace/.env — no per-project .env needed
lake build
```

Lean toolchain: `leanprover/lean4:v4.28.0` · Mathlib: `v4.28.0` · Shared cache: `../.lean-packages/`
