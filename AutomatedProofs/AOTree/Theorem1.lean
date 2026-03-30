import Mathlib
import AutomatedProofs.AOTree.Defs

set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

/-!
# Theorem 1: Hitting Time Upper Bound

Under a policy with minimum correct-tactic probability pₘᵢₙ > 0, and a tree
with shallowest proof of depth d and AND-branching factor ≤ b, the expected
hitting time satisfies:

  E[T] ≤ (1/pₘᵢₙ)^d · b^d

Policy quality enters the *exponent* — halving pₘᵢₙ multiplies E[T] by 2^d.
-/

open NNReal BigOperators AOTree

/-! ## Definitions -/

/-- Minimum probability assigned to any correct child at any OR node on a proof path.
    Defined as the infimum over all such OR nodes; sorry'd here as a placeholder —
    the theorem uses it only as a hypothesis. -/
noncomputable def minProbOnProofPath
    (π : ℕ → ℕ → NNReal) (t : AOTree α) : NNReal :=
  sorry -- defined as inf over OR nodes on proof paths; used only as hypothesis below

/-! ## Key lemma -/

/-- **Lemma 1.1 (success probability lower bound).** For a tree with
    shallowest proof depth ≤ d and AND-branching ≤ b, under a policy that
    assigns ≥ pmin to every correct OR-child on the proof path,
    `successProb π t 0 ≥ (pmin / b) ^ d`.

    PROVIDED SOLUTION
    Proof by structural induction on t.

    Base (leaf): successProb = 1 ≥ (pmin/b)^d requires showing 1 ≥ (pmin/b)^d.
      Since pmin ≤ 1 and b ≥ 1 we have pmin/b ≤ 1, so (pmin/b)^d ≤ 1.
      Use pow_le_one and div_le_one.

    OR node (orNode s cs): successProb = ∑ π(i) * sp(child i).
      The policy assigns ≥ pmin to the best child (the one on the proof path).
      That child has depth ≤ d - 1 and branching ≤ b, so by IH:
        sp(best child) ≥ (pmin/b)^(d-1).
      Since there are ≤ b children and weights sum ≤ 1:
        successProb ≥ pmin · (pmin/b)^(d-1) = (pmin/b)^d · b^(-(d-1)) · b^(-(1))...
      Simplify: pmin · (pmin/b)^(d-1) = pmin^d / b^(d-1).
        We want ≥ (pmin/b)^d = pmin^d / b^d, and b^(d-1) ≤ b^d, so this holds.

    AND node (andNode s cs): successProb = ∏ sp(child i).
      There are ≤ b children, each with depth ≤ d - 1 (since proofDepth andNode ≤ d
      means each child has proofDepth ≤ d - 1).
      By IH each child has sp ≥ (pmin/b)^(d-1).
      The product of b terms each ≥ (pmin/b)^(d-1) is ≥ ((pmin/b)^(d-1))^b.
      Since b*(d-1) = b*d - b ≥ d (for b ≥ 1 and d ≥ 1 ... careful here),
      we have ((pmin/b)^(d-1))^b = (pmin/b)^(b*(d-1)) ≥ (pmin/b)^d.
    KEY LEMMAS: Finset.prod_le_pow_of_le (reversed), pow_mul, Nat.mul_pred_le. -/
lemma successProb_lower_bound
    {α : Type u} (t : AOTree α) (π : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (b : ℕ) (hb : 0 < b)
    (d : ℕ)
    (hpolicy : ∀ nid i, successProb π t nid ≥ pmin)
    (hbranch : maxAndBranch t ≤ b)
    (hdepth : proofDepth t ≤ d) :
    successProb π t 0 ≥ (pmin / b) ^ d := by
  sorry

/-! ## Main theorem -/

/-- **Theorem 1 (hitting time upper bound).** -/
theorem hitting_time_upper_bound
    {α : Type u} (t : AOTree α) (π : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (b d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (hprovable : isProvable t = true)
    (hpolicy : ∀ nid i, successProb π t nid ≥ pmin)
    (hbranch : maxAndBranch t ≤ b)
    (hdepth : proofDepth t ≤ d) :
    (1 : NNReal) / successProb π t 0 ≤ ((1 / pmin) ^ d) * (b : NNReal) ^ d := by
  sorry
  /- PROOF SKETCH (for Aristotle):
     Let hlb := successProb_lower_bound ... to get sp ≥ (pmin/b)^d.
     Note sp > 0 since (pmin/b)^d > 0 (pmin > 0, b > 0).
     Now: 1/sp ≤ 1/(pmin/b)^d = (b/pmin)^d = (1/pmin)^d · b^d.
     Steps:
     1. hpos : sp > 0 from lt_of_lt_of_le (pow_pos ...) hlb.
     2. apply div_le_iff hpos (rearranges to 1 ≤ rhs * sp).
     3. calc: rhs * sp = (1/pmin)^d * b^d * sp
               ≥ (1/pmin)^d * b^d * (pmin/b)^d   [by NNReal.mul_le_mul_left hlb]
             = (1/pmin * b * (pmin/b))^d           [← mul_pow ×2]
             = 1^d = 1.                            [algebra: 1/pmin * b * pmin/b = 1]
     KEY LEMMAS: div_le_iff, mul_pow, NNReal.mul_le_mul_left, div_mul_div_comm,
                 NNReal.div_self. -/

/-- **Corollary (policy quality enters the exponent).**
    A policy π' with min-probability 2·pmin gives E[T'] ≤ (1/2)^d · E[T].

    PROVIDED SOLUTION
    Apply hitting_time_upper_bound to π' with minimum 2·pmin:
      E[T'] ≤ (1/(2·pmin))^d · b^d = (1/2)^d · (1/pmin)^d · b^d.
    Apply hitting_time_upper_bound to π:
      E[T]  ≥ 1 / ((1/pmin)^d · b^d).  [lower bound via 1/ub]
    Combine: E[T'] / E[T] ≤ (1/2)^d. -/
corollary policy_quality_exponent
    {α : Type u} (t : AOTree α) (π π' : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (hpmin2 : 2 * pmin ≤ 1)
    (b d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (hprovable : isProvable t = true)
    (hbranch : maxAndBranch t ≤ b) (hdepth : proofDepth t ≤ d)
    (hπ  : ∀ nid i, successProb π  t nid ≥ pmin)
    (hπ' : ∀ nid i, successProb π' t nid ≥ 2 * pmin) :
    (1 : NNReal) / successProb π' t 0 ≤
      (1 / 2) ^ d * ((1 : NNReal) / successProb π t 0) := by
  sorry
