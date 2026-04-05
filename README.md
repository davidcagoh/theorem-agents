# theorem-agents

**theorem-agents** is an **agentic theorem-proving workspace** for Lean 4. It studies how structured workflows, decomposition strategies, and Aristotle-assisted iterations can be used to develop nontrivial formal proofs.

Where `automated-proofs` provides the reusable infrastructure, `theorem-agents` is the **agent-facing research layer**. It is where proof tasks are organized, decomposed, and pushed through an iterative formalization loop.

## Current focus

The current development formalizes results around **AND/OR tree search, policy quality, and theorem-proving dynamics**. The repository combines Lean formalization with an Aristotle-assisted workflow for managing proof obligations and reducing manual proof burden.

## Repository role in the broader ecosystem

| Repository | Role |
|---|---|
| `automated-proofs` | Reusable workflow and template layer |
| `theorem-agents` | Agentic theorem decomposition and orchestration layer |
| `simplicial-latent-geometry` | Domain-specific mathematical case study |

## What makes this repository distinct

This repository is not just a copy of the proof template. Its purpose is to explore **how theorem work can be organized as an agentic process**.

| Area | Purpose |
|---|---|
| Problem decomposition | Break theorems into Lean-manageable tasks |
| Submission strategy | Package proof jobs into Aristotle-friendly units |
| Proof-state management | Track remaining `sorry`s, open lemmas, and retrieval results |
| Formalization experiments | Explore the boundary between human proof design and automated proof completion |

## Project structure

| Path | Purpose |
|---|---|
| `AutomatedProofs/AOTree/` | Main Lean development for AND/OR tree theorems |
| `my_theorems/` | Markdown theorem papers and proof specifications |
| `scripts/` | Submission, retrieval, status, and watch tooling |
| `reports/` | Annotated result reports |
| `help_from_aristotle/` | Historical job requests and supporting notes |

## Workflow

```bash
lake build
lake build AutomatedProofs.AOTree.Theorem3
python scripts/status.py
python scripts/submit.py my_theorems/lean4_andor_theorems_agent_spec.md "Fill in all the sorries"
python scripts/watch.py
python scripts/retrieve.py
```

## Relationship to the Stochastic Proofs Handbook

This repository follows the broader conventions in the **Stochastic Proofs Handbook**, especially for Lean proof patterns, Aristotle job design, and shared operating guidance. If that shared context is unavailable, the local `CLAUDE.md` and repository files should be treated as authoritative for this project.

## Why keep this separate from `automated-proofs`

This repository deserves to stand on its own because it is a **research project about agentic theorem work**, not merely a reusable template. Keeping it separate preserves its identity as a project about theorem decomposition, workflow design, and proof automation in practice.
