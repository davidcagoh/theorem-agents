# theorem-agents

**theorem-agents** is a Lean 4 formalization project about **stochastic proof search on AND-OR hypertrees**, motivated by neural theorem provers such as **Aristotle**.[1] The repository develops a small theory of expected proof-search time: what determines it, why policy learning helps, where structural hardness comes from, and when sequential lemma decomposition is provably the right architectural response.

Rather than presenting the project as a generic automation template, this repository treats theorem proving as a mathematical object in its own right. The central question is simple: if a proof search procedure repeatedly traverses an AND-OR proof tree under a learned policy, what can be proved about the expected number of traversals required to find a complete proof?

| Repository focus | Description |
|---|---|
| Mathematical setting | AND-OR hypertrees representing proof states, tactic choices, and subgoal decomposition |
| Core quantity | Single-traversal success probability and its reciprocal, the expected hitting time |
| Research motivation | Formal foundations for policy-guided proof search in systems like Aristotle |
| Implementation target | Lean 4 + Mathlib formalization of four linked theorems |
| Portfolio value | Combines formal methods, theorem proving, and theory for agentic search systems |

## Why this project matters

Modern theorem provers increasingly rely on learned policies to prioritize tactics, but policy quality is only part of the story. This project formalizes a broader picture. It shows that **better policies can exponentially improve search in proof depth**, but also that **AND-branching creates structural hardness that no policy can eliminate**. That tension naturally motivates sequential decomposition into lemmas, which the project then analyzes as a provably favorable design choice.

The result is a coherent theoretical narrative rather than four isolated statements. In portfolio terms, the repository showcases work at the intersection of **formal verification**, **learning-theoretic reasoning**, and **agentic system design**.

| Theorem | Main message | Intuition |
|---|---|---|
| **Theorem 1** | Expected hitting time admits an upper bound in terms of proof depth, AND-branching, and minimum policy quality | Better policies help multiplicatively in the exponent |
| **Theorem 2** | Shifting probability mass from incorrect tactics toward correct ones monotonically reduces expected search time | Expert-iteration-style policy improvement is theoretically sound |
| **Theorem 3** | Large AND-branching creates a policy-independent lower bound on hitting time | Some hardness is structural, not algorithmic |
| **Theorem 4** | Sequentially solving independent subgoals is better than attempting them in parallel in the hard-problem regime | Lemma decomposition is not merely heuristic but theoretically justified |

## Mathematical setup

The repository models proof search on a rooted **AND-OR hypertree**. OR nodes represent proof states with alternative tactic choices; AND nodes represent tactic applications that generate multiple subgoals; leaves represent already closed goals. A policy assigns probabilities to children at OR nodes, while AND nodes require all children to succeed.

The key recursive object is the **single-traversal success probability** \(q(t, \pi)\), with expected hitting time \(E[T] = 1 / q(t, \pi)\). This framing turns qualitative questions about proof automation into quantitative, structurally analyzable statements.

| Object | Informal meaning |
|---|---|
| `AOTree` | Lean representation of the proof-search hypertree |
| `successProb` | Probability that one top-down traversal closes the whole tree |
| OR-node policy | Distribution over tactic choices at proof states |
| Expected hitting time | Expected number of traversals until a proof is found |
| `PolicyDominates`-style comparison | Formal way to express policy improvement on correct vs. incorrect tactics |

## The four formalized results

### 1. Hitting-time upper bound

The first theorem proves that if a policy assigns at least some minimum probability to every correct tactic along a proof path, then expected search time is bounded above by a function of proof depth, AND-branching factor, and that minimum policy quality. The important qualitative point is that policy quality enters in the exponent. Even modest policy improvement can therefore produce dramatic search gains on deep proof trees.

### 2. Monotone improvement from better policies

The second theorem formalizes a natural idea behind expert iteration. If a new policy places more weight on correct tactics and less weight on incorrect ones at every relevant OR node, then expected hitting time cannot increase. In other words, policy learning is not only empirically useful; under the model, it is directionally guaranteed to help.

### 3. Policy-independent hardness from AND-branching

The third theorem establishes a lower bound showing that AND-branching can make proof search exponentially hard in the number of simultaneously required subgoals. This matters because it separates two sources of difficulty: bad local choice at OR nodes versus unavoidable structural burden at AND nodes. Even an oracle policy cannot remove the latter.

### 4. Sequential lemma search beats parallel search

The fourth theorem compares two architectures for independent subgoals. In the low-success-probability regime typical of hard mathematical tasks, solving subgoals one at a time yields lower expected search cost than trying to satisfy them all simultaneously in each traversal. This gives a formal justification for sequential lemma decomposition pipelines.[1]

| Relationship | Interpretation |
|---|---|
| Theorem 3 motivates Theorem 4 | Structural AND-hardness explains why decomposition matters |
| Theorem 4 supports Theorem 1 | Sequentialization reduces effective branching and improves the upper bound |
| Theorem 2 strengthens Theorem 1 | Better policies improve the bound without changing tree structure |
| Theorems 1 and 3 together | Upper and lower bounds sandwich the true search difficulty |

## Formalization status

The repository already contains the core Lean definitions and theorem statements for the full AND-OR hypertree program. The main remaining work lies in proof completion for several technically delicate steps, especially weighted-sum monotonicity at OR nodes, product-style induction at AND nodes, and finite combinatorial manipulations used in the sequential-versus-parallel comparison.

That makes this repository a good example of **serious in-progress formalization**: the mathematical story is clear, the target theorems are explicit, and the remaining difficulty is concentrated in meaningful proof engineering rather than project setup.

| Current status area | Notes |
|---|---|
| Core definitions | Implemented for trees, policies, and success probabilities |
| Theorem statements | All four main results are stated in Lean |
| Proof progress | Several supporting lemmas and inductive steps remain under active development |
| Research positioning | The project is already readable as a formal-methods research artifact, not only a codebase |

## Repository structure

The code is organized around the AND-OR hypertree results and their dependencies.

| Path | Role |
|---|---|
| `AOTree/Defs.lean` | Core definitions and shared helper lemmas |
| `AOTree/Theorem3.lean` | Policy-independent hardness from AND-branching |
| `AOTree/Theorem1.lean` | Hitting-time upper bound |
| `AOTree/Theorem4.lean` | Sequential versus parallel search comparison |
| `AOTree/Theorem2.lean` | Monotone policy improvement result |
| `AutomatedProofs.lean` | Entry-point file importing modules in dependency order |
| `scripts/` | Submission, retrieval, status, and watch tooling for the proof workflow |

## Development workflow

The working loop in this repository is intentionally research-oriented. A proof paper or theorem specification is written first, then translated into Lean skeletons with explicit proof sketches, and then iteratively completed using automated theorem proving support where appropriate. The emphasis is on keeping the mathematics legible while still enabling structured proof automation.

| Step | Typical command |
|---|---|
| Build the project | `lake build` |
| Build one theorem file | `lake build AutomatedProofs.AOTree.Theorem3` |
| Check remaining `sorry`s | `python scripts/status.py` |
| Submit a theorem spec | `python scripts/submit.py my_theorems/lean4_andor_theorems_agent_spec.md "Fill in all the sorries"` |
| Watch in-flight jobs | `python scripts/watch.py` |
| Retrieve completed results | `python scripts/retrieve.py` |

## Local setup

The repository is pinned to the same Lean and Mathlib environment used by Aristotle so that returned proofs compile locally without porting friction.[1]

```bash
pip install aristotlelib pathspec python-dotenv

echo "ARISTOTLE_API_KEY=arstl_..." > .env
lake build
```

The project is designed to live inside a shared parent directory such as `~/lean-projects/`, where sibling repositories can reuse the same Mathlib cache.

| Environment component | Version |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.28.0` |
| Mathlib | `v4.28.0` |
| Shared package cache | `../.lean-packages/` |

## Reading this repository as a portfolio piece

If you are visiting this repository from the GitHub profile, the quickest way to understand its value is to read it as a **formal theory of agentic theorem proving**. The project is not just about whether an automated prover can fill `sorry`s. It asks what kinds of architectural and policy improvements should matter in principle, then makes those claims precise in Lean.

For a portfolio, that means the repository demonstrates three things at once: the ability to formulate mathematically interesting questions about modern AI systems, the ability to encode them in a proof assistant, and the ability to structure a repository so that an unfinished formalization is still intelligible and worth reading.

## References

[1]: https://arxiv.org/abs/2510.01346 "Aristotle: Neural theorem proving with Monte Carlo Graph Search"
