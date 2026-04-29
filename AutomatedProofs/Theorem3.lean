import Mathlib
import AutomatedProofs.Defs

set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

/-!
# Theorem 3: AND-Branching Imposes Policy-Independent Hardness

For any policy π with per-child success probability ≤ 1 - ε, and any tree
whose proof passes through an AND node of branching factor b, the expected
number of traversals before finding a proof is at least (1/(1-ε))^b.

**Start here** — this is the simplest of the four theorems and establishes
the core `AOTree` infrastructure for the others.
-/

open NNReal BigOperators AOTree

/-! ## Definitions -/

/-- A tree has an AND node of exactly `b` children on every proof path
    from the root.

    Note: we use `∃ (c : AOTree α) (hc : c ∈ cs), ...` (explicit membership)
    rather than `∃ c ∈ cs, ...` (implicit membership) so that the membership
    proof `hc` is available in the termination proof. -/
def hasAndNodeOfBranching (b : ℕ) : AOTree α → Prop
  | leaf _       => False
  | orNode  _ cs => ∃ (c : AOTree α) (_ : c ∈ cs),
                      isProvable c = true ∧ hasAndNodeOfBranching b c
  | andNode _ cs => cs.length = b ∧ cs.all isProvable
termination_by t => sizeOf t
decreasing_by
  simp_wf
  rename_i hc
  have h := List.sizeOf_lt_of_mem hc
  omega

/-! ## Lemmas -/

/-- `successProb` at an AND node equals the product over children. -/
lemma successProb_andNode_eq
    (π : ℕ → ℕ → NNReal) (s : α) (cs : List (AOTree α)) (nid : ℕ) :
    successProb π (AOTree.andNode s cs) nid =
      ∏ i : Fin cs.length, successProb π (cs.get i) (nid + i.val + 1) := by
  simp [successProb]

/-- If every child of an AND node has success prob ≤ c ≤ 1,
    the node's success prob is ≤ c ^ (number of children). -/
lemma andNode_successProb_le
    (π : ℕ → ℕ → NNReal) (s : α) (cs : List (AOTree α))
    (nid : ℕ) (c : NNReal) (hc : c ≤ 1)
    (hchildren : ∀ i : Fin cs.length,
        successProb π (cs.get i) (nid + i.val + 1) ≤ c) :
    successProb π (AOTree.andNode s cs) nid ≤ c ^ cs.length := by
  rw [successProb_andNode_eq]
  exact NNReal.prod_le_pow_of_le _ c hc hchildren

/-! ## Main theorem -/

/-- **Theorem 3 (AND-branching lower bound).** If the tree requires passing
    through an AND node of branching factor b, and the root's single-traversal
    success probability is ≤ (1 - ε)^b for every node-ID offset, then the
    expected hitting time is ≥ (1/(1-ε))^b.

    The hypothesis `hpmax` bounds `successProb π t nid` for all node IDs `nid`.
    In typical usage one first establishes per-child bounds ≤ 1 - ε at the AND
    node and then applies `andNode_successProb_le` to obtain the (1-ε)^b bound
    before invoking this theorem. -/
theorem and_branching_lower_bound
    {α : Type u} (t : AOTree α)
    (π : ℕ → ℕ → NNReal)
    (b : ℕ) (hb : b ≥ 1)
    (ε : NNReal) (hε : 0 < ε) (hε1 : ε < 1)
    (hpmax : ∀ (nid : ℕ), successProb π t nid ≤ (1 - ε) ^ b)
    (hbranch : hasAndNodeOfBranching b t)
    (hsp : 0 < successProb π t 0) :
    (1 : NNReal) / successProb π t 0 ≥ (1 / (1 - ε)) ^ b := by
  -- Step 1: successProb π t 0 ≤ (1 - ε)^b
  have hle : successProb π t 0 ≤ (1 - ε) ^ b := hpmax 0
  -- Step 2: rewrite goal and apply inv_anti₀
  rw [ge_iff_le, one_div, one_div, inv_pow]
  exact inv_anti₀ hsp hle

-- As b → ∞, the hitting time is unbounded (for any fixed ε > 0).
theorem and_branching_unbounded
    {α : Type u} (ε : NNReal) (hε : 0 < ε) (hε1 : ε < 1)
    (makeTree : ℕ → AOTree α)
    (π : ℕ → ℕ → ℕ → NNReal)
    (hbranch : ∀ b, hasAndNodeOfBranching b (makeTree b))
    (hpmax : ∀ b nid, successProb (π b) (makeTree b) nid ≤ (1 - ε) ^ b)
    (hsp : ∀ b, 0 < successProb (π b) (makeTree b) 0) :
    Filter.Tendsto (fun b => (1 : NNReal) / successProb (π b) (makeTree b) 0)
      Filter.atTop Filter.atTop := by
  -- Step 1: r = 1/(1-ε) > 1
  have hpos_sub : (0 : NNReal) < 1 - ε := tsub_pos_of_lt hε1
  have hr : 1 < 1 / (1 - ε) := by
    rw [one_lt_div₀ hpos_sub]
    exact tsub_lt_self one_pos hε
  -- Step 2: r^b → ∞
  have htend : Filter.Tendsto (fun b => (1 / (1 - ε)) ^ b) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hr
  -- Step 3: the hitting time at b is ≥ r^b
  have hbound : ∀ b, (1 / (1 - ε)) ^ b ≤ 1 / successProb (π b) (makeTree b) 0 := by
    intro b
    rcases Nat.eq_zero_or_pos b with rfl | hbpos
    · -- b = 0: (1/(1-ε))^0 = 1 ≤ 1/sp (since sp ≤ 1)
      simp only [pow_zero]
      rw [le_div_iff₀ (hsp 0)]
      have h0 := hpmax 0 0
      simp only [pow_zero] at h0
      calc 1 * successProb (π 0) (makeTree 0) 0
          = successProb (π 0) (makeTree 0) 0 := one_mul _
        _ ≤ 1 := h0
    · exact and_branching_lower_bound (makeTree b) (π b) b hbpos ε hε hε1
        (fun nid => hpmax b nid) (hbranch b) (hsp b)
  -- Step 4: apply tendsto_atTop_mono
  exact Filter.tendsto_atTop_mono hbound htend
