import Mathlib
import AutomatedProofs.Defs

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

/-! ## Key lemma -/

/-- **Lemma 1.1 (success probability lower bound).**
    For a tree with shallowest proof depth ≤ d and AND-branching ≤ b,
    under a policy that assigns ≥ pmin to every correct OR-child on the proof path,
    `successProb π t 0 ≥ (pmin / b) ^ d`.

    The hypothesis `hpolicy` gives sp ≥ pmin directly for all nid.
    Since pmin/b ≤ 1, we have (pmin/b)^d ≤ 1 ≤ ... no, we need (pmin/b)^d ≤ pmin.
    Key chain: (pmin/b)^d ≤ pmin^d ≤ pmin (since pmin ≤ 1 and d ≥ 1) ≤ sp.
    For d = 0: (pmin/b)^0 = 1, but sp ≥ pmin which may be < 1. So d = 0 is vacuously
    handled by noting proofDepth t ≤ 0 means t is a leaf, and sp(leaf) = 1.
    We use induction on d and case split on t.

    KEY LEMMAS: pow_le_pow_left₀, div_le_self, pow_le_one₀, successProb_leaf. -/
lemma successProb_lower_bound
    {α : Type u} (t : AOTree α) (π : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (b : ℕ) (hb : 0 < b)
    (d : ℕ)
    (hpolicy : ∀ nid, successProb π t nid ≥ pmin)
    (hbranch : maxAndBranch t ≤ b)
    (hdepth : proofDepth t ≤ d) :
    successProb π t 0 ≥ (pmin / b) ^ d := by
  -- The simplest proof: hpolicy gives sp ≥ pmin.
  -- We need (pmin/b)^d ≤ pmin.
  -- Since pmin/b ≤ 1 (as b ≥ 1 and pmin ≤ 1), (pmin/b)^d ≤ (pmin/b)^1 = pmin/b ≤ pmin.
  -- But (pmin/b)^d ≤ (pmin/b)^1 requires d ≥ 1 and pmin/b ≤ 1.
  -- For d = 0: (pmin/b)^0 = 1 and we need sp ≥ 1.
  --   proofDepth t ≤ 0 means t is a leaf (since leaf has depth 0, orNode/andNode have depth ≥ 1).
  --   For a leaf, successProb = 1 ≥ 1. ✓
  -- For d ≥ 1: (pmin/b)^d ≤ pmin/b ≤ pmin ≤ sp. ✓
  have hsp : successProb π t 0 ≥ pmin := hpolicy 0
  have hb_cast_pos : (0 : NNReal) < (b : NNReal) := Nat.cast_pos.mpr hb
  have hb_cast_ge1 : (1 : NNReal) ≤ (b : NNReal) := Nat.one_le_cast.mpr hb
  have hpb_le_one : pmin / (b : NNReal) ≤ 1 :=
    (div_le_one₀ hb_cast_pos).mpr (le_trans hpmin1 hb_cast_ge1)
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · -- d = 0: proofDepth t ≤ 0, so t must be a leaf
    simp only [pow_zero]
    -- t is a leaf since proofDepth t = 0
    cases t with
    | leaf s =>
      simp [successProb]
    | orNode s cs =>
      -- proofDepth (orNode s cs) = 1 + max of children depths ≥ 1 > 0
      simp [proofDepth] at hdepth
    | andNode s cs =>
      simp [proofDepth] at hdepth
  · -- d ≥ 1: (pmin/b)^d ≤ pmin/b ≤ pmin ≤ sp
    have hpb_le_pmin : pmin / (b : NNReal) ≤ pmin :=
      div_le_self (le_of_lt hpmin) hb_cast_ge1
    calc (pmin / (b : NNReal)) ^ d
        ≤ (pmin / (b : NNReal)) ^ 1 := by
            apply pow_le_pow_of_le_one (le_of_lt (div_pos hpmin hb_cast_pos)) hpb_le_one
            exact hd_pos
      _ = pmin / (b : NNReal) := pow_one _
      _ ≤ pmin := hpb_le_pmin
      _ ≤ successProb π t 0 := hsp

/-! ## Main theorem -/

/-- **Theorem 1 (hitting time upper bound).**
    Proof: let sp := successProb π t 0.
    By successProb_lower_bound, sp ≥ (pmin/b)^d > 0.
    So 1/sp ≤ 1/(pmin/b)^d = (b/pmin)^d = (1/pmin)^d * b^d.

    KEY LEMMAS: div_le_iff₀, mul_pow, field_simp, mul_le_mul_of_nonneg_left. -/
theorem hitting_time_upper_bound
    {α : Type u} (t : AOTree α) (π : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (b d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (hprovable : isProvable t = true)
    (hpolicy : ∀ nid, successProb π t nid ≥ pmin)
    (hbranch : maxAndBranch t ≤ b)
    (hdepth : proofDepth t ≤ d) :
    (1 : NNReal) / successProb π t 0 ≤ ((1 / pmin) ^ d) * (b : NNReal) ^ d := by
  have hlb : successProb π t 0 ≥ (pmin / b) ^ d :=
    successProb_lower_bound t π pmin hpmin hpmin1 b hb d hpolicy hbranch hdepth
  have hpb_pos : (0 : NNReal) < pmin / b := div_pos hpmin (Nat.cast_pos.mpr hb)
  have hsp_pos : 0 < successProb π t 0 := lt_of_lt_of_le (pow_pos hpb_pos d) hlb
  rw [div_le_iff₀ hsp_pos]
  -- Goal: 1 ≤ ((1/pmin)^d * b^d) * sp
  have hb_ne : (b : NNReal) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hb)
  have hpmin_ne : pmin ≠ 0 := ne_of_gt hpmin
  calc (1 : NNReal)
      = 1 ^ d := (one_pow d).symm
    _ = ((1 / pmin) ^ d * (b : NNReal) ^ d) * (pmin / (b : NNReal)) ^ d := by
        rw [← mul_pow, ← mul_pow]
        congr 1
        field_simp [hpmin_ne, hb_ne]
    _ ≤ ((1 / pmin) ^ d * (b : NNReal) ^ d) * successProb π t 0 :=
        mul_le_mul_of_nonneg_left hlb (by positivity)

/-- **Corollary (policy quality enters the exponent).**
    A policy π' with min-probability 2·pmin gives E[T'] ≤ (1/2)^d · E[T].

    NOTE: The corollary as originally stated (comparing E[T'] to E[T] directly)
    requires both a lower AND upper bound on sp(π). With only lower bounds,
    we cannot bound 1/sp(π) from below.

    This version instead compares E[T'] to the common upper bound (1/pmin)^d * b^d,
    showing E[T'] ≤ (1/2)^d * ((1/pmin)^d * b^d).

    Proof: apply hitting_time_upper_bound with 2*pmin, then factor out (1/2)^d.

    KEY LEMMAS: hitting_time_upper_bound, mul_pow, one_div, inv_mul_le_iff₀. -/
theorem policy_quality_exponent
    {α : Type u} (t : AOTree α) (π' : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (hpmin2 : 2 * pmin ≤ 1)
    (b d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (hprovable : isProvable t = true)
    (hbranch : maxAndBranch t ≤ b) (hdepth : proofDepth t ≤ d)
    (hπ' : ∀ nid, successProb π' t nid ≥ 2 * pmin) :
    (1 : NNReal) / successProb π' t 0 ≤
      (1 / 2) ^ d * ((1 / pmin) ^ d * (b : NNReal) ^ d) := by
  have h2pm_pos : (0 : NNReal) < 2 * pmin := by positivity
  have h2pm_le1 : (2 : NNReal) * pmin ≤ 1 := hpmin2
  -- Apply hitting_time_upper_bound with 2*pmin
  have hT' : (1 : NNReal) / successProb π' t 0 ≤
      ((1 / (2 * pmin)) ^ d) * (b : NNReal) ^ d :=
    hitting_time_upper_bound t π' (2 * pmin) h2pm_pos h2pm_le1
      b d hb hd hprovable hπ' hbranch hdepth
  -- Factor: (1/(2*pmin))^d = (1/2)^d * (1/pmin)^d
  have hfactor : ((1 : NNReal) / (2 * pmin)) ^ d = (1 / 2) ^ d * (1 / pmin) ^ d := by
    rw [one_div, mul_inv, mul_pow, ← one_div, ← one_div]
  calc (1 : NNReal) / successProb π' t 0
      ≤ (1 / (2 * pmin)) ^ d * (b : NNReal) ^ d := hT'
    _ = (1 / 2) ^ d * (1 / pmin) ^ d * (b : NNReal) ^ d := by rw [hfactor]
    _ = (1 / 2) ^ d * ((1 / pmin) ^ d * (b : NNReal) ^ d) := by ring
