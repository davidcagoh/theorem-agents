import Mathlib
import AutomatedProofs.AOTree.Defs
import AutomatedProofs.AOTree.Theorem4

set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

/-!
# Theorem 4 (strong form): Sharp regime for sequential ≤ parallel

The original `sequential_le_parallel` requires `q(i) ≤ 1/2` for every `i`. A
counter-example at `q(0) = q(1) = 3/4` shows that the inequality reverses when
all `q` values exceed 1/2 sufficiently. However, the sharp threshold is
`∑ q(i) ≤ 1` — strictly weaker than uniform `q(i) ≤ 1/2`.

Verification at `n = 2`:
  ∑ prod_erase = q(1) + q(0) = q(0) + q(1) ≤ 1  iff  ∑ q(i) ≤ 1. ✓

This gives a meaningfully larger regime: for instance `q(0) = 0.9, q(1) = 0.05,
q(2) = 0.05` satisfies the sharper condition (sum = 1.0) but violates uniform
`q(i) ≤ 1/2` (first q is 0.9).

The proof strategy uses the AM-GM-style identity
  (∑ 1/q_i) · ∏ q_j = ∑ ∏_{j ≠ i} q_j
combined with a symmetric function argument: under `∑ q_i ≤ 1`, the elementary
symmetric polynomial `e_{n-1}(q)` is bounded by `(∑ q)^{n-1} / (n-1)!` (Maclaurin's
inequality) or equivalently via iterated AM-GM.
-/

open NNReal BigOperators AOTree

/-- **Lemma 4.1 (strong).** Sharp sum-product-erase bound: under `∑ q_i ≤ 1`
    (rather than the uniform `q_i ≤ 1/2`), the sum of products-with-one-erased
    is still bounded by 1.

    Sketch: use Maclaurin's inequality — for non-negative reals,
      e_{n-1}(q) / C(n, n-1) ≤ (e_1(q) / C(n,1))^{n-1}
    which gives
      ∑_i ∏_{j ≠ i} q_j = e_{n-1}(q) ≤ n · (∑ q_i / n)^{n-1} ≤ n · (1/n)^{n-1} ≤ 1.

    Alternative: direct induction on n, using the convexity identity
      ∑ ∏_{j ≠ i} q_j = (∑ q_i) · ∏ q_i · [1 + ...]
    An explicit computation for n=2 is q_0 + q_1 ≤ 1 ✓; for n ≥ 3 iterate.

    KEY MATHLIB LEMMAS: `Finset.inner_mul_le_norm_mul_norm`, `Finset.prod_le_prod`,
    `NNReal.pow_le_pow_of_le_one`, `Finset.sum_le_sum`. May need
    `Finset.geom_mean_le_arith_mean_weighted` or equivalent Maclaurin result from
    Mathlib. -/
lemma sum_prod_erase_le_one_of_sum_le_one
    {n : ℕ} (hn : n ≥ 2) (q : Fin n → NNReal)
    (hsum : (∑ i, q i) ≤ 1) :
    ∑ i, (∏ j ∈ Finset.univ.erase i, q j) ≤ 1 := by
  sorry

/-- **Theorem 4 (strong).** Sequential ≤ parallel under the sharp condition
    `∑ q(i) ≤ 1`.

    This supersedes `sequential_le_parallel` (which requires uniform
    `q(i) ≤ 1/2`), since `q(i) ≤ 1/2` for all `i` implies `∑ q(i) ≤ n · (1/2)`,
    which is NOT the same condition (the uniform version can handle larger
    sums when n is small). The two conditions are incomparable for `n ≥ 3`:
    `∑ q(i) ≤ 1` handles heavy-tailed distributions, uniform `q(i) ≤ 1/2`
    handles more-uniform-but-larger ones.

    The statement here captures the heavy-tailed regime exactly. -/
theorem sequential_le_parallel_sharp
    {n : ℕ} (hn : n ≥ 2) (q : Fin n → NNReal)
    (hqpos : ∀ i, 0 < q i)
    (hsum : (∑ i, q i) ≤ 1) :
    ∑ i, (1 / q i) ≤ ∏ i, (1 / q i) := by
  -- Reduce to sum_prod_erase_le_one_of_sum_le_one as in the original proof.
  -- The skeleton mirrors `sequential_le_parallel` in Theorem4.lean; the only
  -- replacement is the invocation of `sum_prod_erase_le_one_of_sum_le_one`
  -- instead of `sum_prod_erase_le_one`.
  sorry
