import Mathlib
import AutomatedProofs.AOTree.Defs

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
    through an AND node of branching factor b, and every child closes with
    probability ≤ 1 - ε, then the expected hitting time is ≥ (1/(1-ε))^b.

    Note on `hpmax`: this hypothesis bounds `successProb π t nid` for all
    node IDs `nid`, treating `t` as the fixed root tree. For the andNode case
    this gives bounds on children via `hpmax (nid + i + 1) i`. For the orNode
    case `hpmax 0 0` gives successProb ≤ 1-ε, but we need ≤ (1-ε)^b; since
    (1-ε)^b ≤ 1-ε when b ≥ 1 and 1-ε ≤ 1, the inequality goes the wrong way.
    The orNode case is left as sorry; the theorem statement needs a stronger
    hypothesis (e.g., hpmax applied to subtrees, not just the root).

    Note on `hpmax` for andNode children: `hpmax` bounds `successProb π t nid`
    where `t` is the root tree (andNode s cs). The children are `cs.get i`,
    which are subtrees of `t`. We need `successProb π (cs.get i) nid ≤ 1-ε`
    but `hpmax` gives `successProb π (andNode s cs) nid ≤ 1-ε`. These are
    different. The andNode case also needs a stronger hypothesis. Left as sorry.

    Proof structure (both cases sorry due to hpmax scoping):
    Step 1: `cs.length = b` from `simp [hasAndNodeOfBranching] at hb`.
    Step 2: Each child has successProb ≤ 1-ε (needs stronger hpmax).
    Step 3: `NNReal.prod_le_pow_of_le` gives successProb ≤ (1-ε)^b.
    Step 4: `inv_anti₀ hsp hle` gives (1-ε)⁻¹^b ≤ sp⁻¹.
    KEY LEMMAS: NNReal.prod_le_pow_of_le, tsub_pos_of_lt, pow_pos,
                inv_anti₀, inv_pow, one_div_pow, one_lt_div₀, tsub_lt_self,
                tendsto_pow_atTop_atTop_of_one_lt. -/
theorem and_branching_lower_bound
    {α : Type u} (t : AOTree α)
    (π : ℕ → ℕ → NNReal)
    (b : ℕ) (hb : b ≥ 1)
    (ε : NNReal) (hε : 0 < ε) (hε1 : ε < 1)
    (hpmax : ∀ (nid : ℕ) (i : ℕ), successProb π t nid ≤ 1 - ε)
    (hbranch : hasAndNodeOfBranching b t)
    (hsp : 0 < successProb π t 0) :
    (1 : NNReal) / successProb π t 0 ≥ (1 / (1 - ε)) ^ b := by
  -- Step 1: successProb π t 0 ≤ (1 - ε)^b
  have hle : successProb π t 0 ≤ (1 - ε) ^ b := by
    match t, hbranch with
    | AOTree.leaf _, hb => exact absurd hb (by simp [hasAndNodeOfBranching])
    | AOTree.orNode s cs, hb =>
      -- hpmax gives sp ≤ 1-ε, but we need sp ≤ (1-ε)^b.
      -- Since b ≥ 1 and 1-ε ≤ 1, (1-ε)^b ≤ 1-ε (wrong direction).
      -- Needs stronger hypothesis: hpmax for subtrees. Left as sorry.
      sorry
    | AOTree.andNode s cs, hb =>
      -- hb : hasAndNodeOfBranching b (andNode s cs)
      -- Unfold to get: cs.length = b ∧ cs.all isProvable
      simp only [hasAndNodeOfBranching] at hb
      obtain ⟨hlen, _⟩ := hb
      rw [successProb_andNode_eq, ← hlen]
      apply NNReal.prod_le_pow_of_le
      · exact tsub_le_self  -- 1 - ε ≤ 1
      · intro i
        -- Need: successProb π (cs.get i) (0 + i.val + 1) ≤ 1 - ε
        -- hpmax gives: successProb π (andNode s cs) (0 + i.val + 1) ≤ 1 - ε
        -- These are different: hpmax is about the root tree, not subtrees.
        -- Needs stronger hypothesis. Left as sorry.
        sorry
  -- Step 2: rewrite goal and apply inv_anti₀
  rw [ge_iff_le, one_div, one_div, inv_pow]
  exact inv_anti₀ hsp hle

-- As b → ∞, the hitting time is unbounded (for any fixed ε > 0).
theorem and_branching_unbounded
    {α : Type u} (ε : NNReal) (hε : 0 < ε) (hε1 : ε < 1)
    (makeTree : ℕ → AOTree α)
    (π : ℕ → ℕ → ℕ → NNReal)
    (hbranch : ∀ b, hasAndNodeOfBranching b (makeTree b))
    (hpmax : ∀ b nid, successProb (π b) (makeTree b) nid ≤ 1 - ε)
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
      calc (1 : NNReal) * successProb (π 0) (makeTree 0) 0
          ≤ 1 * (1 - ε) := mul_le_mul_of_nonneg_left (hpmax 0 0) zero_le_one
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left tsub_le_self zero_le_one
        _ = 1 := one_mul 1
    · exact and_branching_lower_bound (makeTree b) (π b) b hbpos ε hε hε1
        (fun nid _ => hpmax b nid) (hbranch b) (hsp b)
  -- Step 4: apply tendsto_atTop_mono
  exact Filter.tendsto_atTop_mono hbound htend
