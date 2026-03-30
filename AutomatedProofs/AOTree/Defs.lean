import Mathlib

set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# AND-OR Hypertree Definitions

Shared infrastructure for the four AND-OR hypertree hitting-time theorems.
We formalize `AOTree`, `successProb`, and OR-node policies, then prove two
helper lemmas used across all theorems.

## Design choices

- `NNReal` throughout to avoid subtraction issues.
- Trees are a plain inductive type with `List` children; no measure theory needed.
- `successProb` is a plain `NNReal`-valued function satisfying the recursion by construction.
- `isProvable` uses `List.attach` (not `List.any/all`) to avoid requiring `BEq (AOTree α)`.
- Policies are functions `ℕ → ℕ → NNReal` (nodeId → childIdx → weight);
  well-formedness (weights sum to 1) is a hypothesis, not baked into the type.
-/

open NNReal BigOperators

/-! ## Tree type -/

universe u

/-- A finite AND-OR hypertree over states of type `α`. -/
inductive AOTree (α : Type u) : Type u
  /-- Leaf: an axiom, trivially closed. -/
  | leaf    : α → AOTree α
  /-- OR node: closed if ANY child closes. -/
  | orNode  : α → List (AOTree α) → AOTree α
  /-- AND node: closed only if ALL children close. -/
  | andNode : α → List (AOTree α) → AOTree α
  deriving Repr

namespace AOTree

variable {α : Type u}

/-- Depth = length of longest root-to-leaf path. -/
def depth : AOTree α → ℕ
  | leaf _       => 0
  | orNode  _ cs => 1 + (cs.map depth).foldr max 0
  | andNode _ cs => 1 + (cs.map depth).foldr max 0

/-- Maximum AND-branching factor over all nodes. -/
def maxAndBranch : AOTree α → ℕ
  | leaf _       => 0
  | orNode  _ cs => (cs.map maxAndBranch).foldr max 0
  | andNode _ cs => max cs.length ((cs.map maxAndBranch).foldr max 0)

/-- A tree is provable if all leaves close, OR nodes have a provable child,
    AND nodes have all children provable.
    Uses `List.attach` to avoid requiring `BEq (AOTree α)`. -/
def isProvable : AOTree α → Bool
  | leaf _       => true
  | orNode  _ cs => cs.attach.any  (fun ⟨c, _⟩ => isProvable c)
  | andNode _ cs => cs.attach.all  (fun ⟨c, _⟩ => isProvable c)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals (have h := List.sizeOf_lt_of_mem (by assumption); omega)

end AOTree

/-- Shallowest proof depth: minimum depth of any complete proof subtree.
    Uses `depth` as a conservative upper bound at OR nodes (suffices for Theorem 1). -/
noncomputable def AOTree.proofDepth {α : Type u} : AOTree α → ℕ
  | AOTree.leaf _       => 0
  | AOTree.orNode  _ cs =>
      let depths := (cs.filter AOTree.isProvable).map AOTree.proofDepth
      1 + match depths with
          | []      => 0
          | d :: ds => ds.foldl min d
  | AOTree.andNode _ cs => 1 + (cs.map AOTree.proofDepth).foldr max 0

/-! ## Policies -/

/-- OR-policy on a node with `n` children: weight vector over child indices. -/
def ORPolicy (n : ℕ) : Type := Fin n → NNReal

/-- Well-formedness: weights sum to 1. -/
def ORPolicy.WF {n : ℕ} (π : ORPolicy n) : Prop :=
  ∑ i : Fin n, π i = 1

/-! ## Success probability -/

/-- Single-traversal success probability under policy `π`.

    `π nodeId childIdx` = weight on child `childIdx` at node `nodeId`.
    Node IDs are assigned by depth-first pre-order (root = 0).
    At AND nodes `π` is ignored; all children must close.
-/
noncomputable def successProb {α : Type u}
    (π : ℕ → ℕ → NNReal) : AOTree α → ℕ → NNReal
  | AOTree.leaf _,       _   => 1
  | AOTree.orNode  _ cs, nid =>
      ∑ i : Fin cs.length,
        π nid i.val * successProb π (cs.get i) (nid + i.val + 1)
  | AOTree.andNode _ cs, nid =>
      ∏ i : Fin cs.length,
        successProb π (cs.get i) (nid + i.val + 1)
termination_by t _ => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals (
    have hmem := List.getElem_mem (l := cs) i.isLt
    have h := List.sizeOf_lt_of_mem hmem
    omega)

/-! ## Helper lemmas (not in Mathlib) -/

/-- If each factor in a finite product is ≤ c and c ≤ 1,
    the product is ≤ c ^ n. -/
lemma NNReal.prod_le_pow_of_le
    {n : ℕ} (f : Fin n → NNReal) (c : NNReal)
    (hc : c ≤ 1) (hf : ∀ i, f i ≤ c) :
    ∏ i, f i ≤ c ^ n := by
  calc ∏ i : Fin n, f i
      ≤ ∏ _i : Fin n, c := by
          apply Finset.prod_le_prod
          · intro i _; exact zero_le _
          · intro i _; exact hf i
    _ = c ^ n := by simp [Finset.prod_const]

/-- **Helper Lemma A (sum-prod-erase).** For n ≥ 2 factors each ≤ 1/2,
    the sum of (n-1)-fold products (each omitting one factor) is ≤ 1.

    PROVIDED SOLUTION
    Step 1: Induction on n. Base case n = 2: the sum is q 1 + q 0,
            and each is ≤ 1/2, so the sum is ≤ 1.
    Step 2: Inductive step n → n+1. Split the outer sum at the last index.
            The last term contributes ∏_{j < n} q j ≤ (1/2)^n ≤ 1/2
            (by NNReal.prod_le_pow_of_le).
    Step 3: The remaining n terms each gain a factor of q(last) ≤ 1/2
            from the new last element, so their sum is
            q(last) · (∑_{i < n} ∏_{j ≠ i, j < n} q j) ≤ q(last) · 1 ≤ 1/2
            by the inductive hypothesis.
    Step 4: Total ≤ 1/2 + 1/2 = 1.
    KEY LEMMAS: Fin.prod_univ_castSucc, Fin.sum_univ_castSucc,
                NNReal.prod_le_pow_of_le. -/
lemma sum_prod_erase_le_one
    {n : ℕ} (hn : n ≥ 2) (q : Fin n → NNReal)
    (hq : ∀ i, q i ≤ 1 / 2) :
    ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q j) ≤ 1 := by
  sorry

/-- **Helper Lemma B (weighted-sum monotonicity).** Shifting policy weight toward
    higher-valued choices increases the weighted sum.

    PROVIDED SOLUTION
    Step 1: Write the difference ∑ w' f - ∑ w f = ∑ (w' i - w i) * f i.
    Step 2: Since ∑ w' = ∑ w = 1, the weight shifts sum to zero:
            ∑_{good} (w' i - w i) = -∑_{bad} (w' i - w i).
    Step 3: On good indices w' i ≥ w i so the good-weight shift is non-negative.
            On bad indices f i ≤ f j for j ∈ good (by hbetter), and the
            bad-weight shift is non-positive.
    Step 4: Conclude the difference is ≥ 0 by a rearrangement / pairing argument.
    KEY LEMMAS: Finset.sum_sub_distrib, Finset.sum_compl_add_sum. -/
lemma NNReal.weighted_sum_mono
    {n : ℕ} (w w' : Fin n → NNReal)
    (hw  : ∑ i, w  i = 1) (hw' : ∑ i, w' i = 1)
    (f   : Fin n → NNReal)
    (good : Finset (Fin n))
    (hshift  : ∀ i ∈ good, w i ≤ w' i)
    (hbetter : ∀ i ∉ good, ∀ j ∈ good, f i ≤ f j) :
    ∑ i, w i * f i ≤ ∑ i, w' i * f i := by
  sorry
