import Mathlib
import AutomatedProofs.Defs
import AutomatedProofs.Theorem1

set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

/-!
# Theorem 1 (strong form): Hitting-Time Upper Bound with Root-Only Hypothesis

This file strengthens `hitting_time_upper_bound` in `Theorem1.lean` by replacing
the uniform hypothesis `∀ nid, successProb π t nid ≥ pmin` with the weaker
root-only hypothesis `successProb π t 0 ≥ pmin`.

The original proof in `Theorem1.lean` uses `hpolicy` only at `nid = 0` (one
occurrence in `successProb_lower_bound`, line 54). The strong variant below is
a direct simplification of that proof.

The original `hitting_time_upper_bound` then becomes an immediate corollary of
this strong form (uniform ⇒ root).
-/

open NNReal BigOperators AOTree

/-- **Lemma 1.1 (strong).** Root-only variant of `successProb_lower_bound`:
    the bound $(p_{\min}/b)^d \le \mathrm{sp}(\pi,t,0)$ follows from the
    root-only hypothesis `successProb π t 0 ≥ pmin`. -/
lemma successProb_lower_bound_root
    {α : Type u} (t : AOTree α) (π : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (b : ℕ) (hb : 0 < b)
    (d : ℕ)
    (hpolicy_root : successProb π t 0 ≥ pmin)
    (hdepth : proofDepth t ≤ d) :
    successProb π t 0 ≥ (pmin / b) ^ d := by
  have hb_cast_pos : (0 : NNReal) < (b : NNReal) := Nat.cast_pos.mpr hb
  have hb_cast_ge1 : (1 : NNReal) ≤ (b : NNReal) := Nat.one_le_cast.mpr hb
  have hpb_le_one : pmin / (b : NNReal) ≤ 1 :=
    (div_le_one₀ hb_cast_pos).mpr (le_trans hpmin1 hb_cast_ge1)
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · simp only [pow_zero]
    cases t with
    | leaf s => simp [successProb]
    | orNode s cs => simp [proofDepth] at hdepth
    | andNode s cs => simp [proofDepth] at hdepth
  · have hpb_le_pmin : pmin / (b : NNReal) ≤ pmin :=
      div_le_self (le_of_lt hpmin) hb_cast_ge1
    calc (pmin / (b : NNReal)) ^ d
        ≤ (pmin / (b : NNReal)) ^ 1 := by
            apply pow_le_pow_of_le_one (le_of_lt (div_pos hpmin hb_cast_pos)) hpb_le_one
            exact hd_pos
      _ = pmin / (b : NNReal) := pow_one _
      _ ≤ pmin := hpb_le_pmin
      _ ≤ successProb π t 0 := hpolicy_root

/-- **Theorem 1 (strong).** Hitting-time upper bound with root-only hypothesis.

    This is the strengthened form of `hitting_time_upper_bound`: the uniform
    quantifier `∀ nid, successProb π t nid ≥ pmin` is replaced by the root-only
    `successProb π t 0 ≥ pmin`. The conclusion is identical.

    The `hprovable` and `hbranch` hypotheses of the original theorem are not
    needed in this proof (they were interface-level, not proof-load-bearing).
    We drop them here to present the cleanest statement.
-/
theorem hitting_time_upper_bound_root
    {α : Type u} (t : AOTree α) (π : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (b d : ℕ) (hb : 0 < b) (_hd : 0 < d)
    (hpolicy_root : successProb π t 0 ≥ pmin)
    (hdepth : proofDepth t ≤ d) :
    (1 : NNReal) / successProb π t 0 ≤ ((1 / pmin) ^ d) * (b : NNReal) ^ d := by
  have hlb : successProb π t 0 ≥ (pmin / b) ^ d :=
    successProb_lower_bound_root t π pmin hpmin hpmin1 b hb d hpolicy_root hdepth
  have hpb_pos : (0 : NNReal) < pmin / b := div_pos hpmin (Nat.cast_pos.mpr hb)
  have hsp_pos : 0 < successProb π t 0 := lt_of_lt_of_le (pow_pos hpb_pos d) hlb
  rw [div_le_iff₀ hsp_pos]
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

/-- The original `hitting_time_upper_bound` is an immediate corollary of the
    strong form: a uniform lower bound on `successProb` at every `nid` implies
    the root bound. -/
theorem hitting_time_upper_bound_from_strong
    {α : Type u} (t : AOTree α) (π : ℕ → ℕ → NNReal)
    (pmin : NNReal) (hpmin : 0 < pmin) (hpmin1 : pmin ≤ 1)
    (b d : ℕ) (hb : 0 < b) (hd : 0 < d)
    (hpolicy : ∀ nid, successProb π t nid ≥ pmin)
    (hdepth : proofDepth t ≤ d) :
    (1 : NNReal) / successProb π t 0 ≤ ((1 / pmin) ^ d) * (b : NNReal) ^ d :=
  hitting_time_upper_bound_root t π pmin hpmin hpmin1 b d hb hd (hpolicy 0) hdepth
