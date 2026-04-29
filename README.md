# stochastic-search-bounds

Lean 4 formalization of hitting-time theorems for policy-guided AND/OR hypertree search — the theoretical foundation for neural theorem-proving complexity. Part of the [Stochastic Proofs](../stochastic-proofs-handbook) workspace.

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
