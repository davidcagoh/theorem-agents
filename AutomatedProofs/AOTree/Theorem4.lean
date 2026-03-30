import Mathlib
import AutomatedProofs.AOTree.Defs

set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

/-!
# Theorem 4: Sequential Search Dominates Parallel

For b ≥ 2 independent subgoals with closure probabilities q₁, …, qb ∈ (0, 1/2],
sequential expected total trials satisfies:

  ∑ᵢ 1/qᵢ  ≤  ∏ᵢ 1/qᵢ

i.e. the sum of reciprocals is at most their product.
This means searching subgoals one-at-a-time is never worse than parallel search.
-/

open NNReal BigOperators

/-! ## Core algebraic lemma -/

/-- **Lemma 4.1 (sum-prod-erase ≤ 1).** For n ≥ 2 factors each ≤ 1/2,
    the sum over i of (the product over j with factor i replaced by 1) is ≤ 1.

    This is the algebraic heart of Theorem 4; it implies ∑ 1/qᵢ ≤ ∏ 1/qᵢ.

    PROVIDED SOLUTION
    Induction on n.
    Base (n = 2): the sum is q 1 + q 0 (by Fin.sum/prod_univ_two).
      Each is ≤ 1/2, so the sum ≤ 1. Done by add_le_one from hq 0, hq 1.
    Step (n → n+1): use Fin.sum_univ_castSucc and Fin.prod_univ_castSucc
      to peel off the last index.
      * Last term: ∏_{j < n} q j  ≤  (1/2)^n  ≤  1/2
        (by NNReal.prod_le_pow_of_le and pow_le_one).
      * Remaining n terms: each inner product gains factor q(last) ≤ 1/2, so
          q(last) · ∑_{i < n} ∏_{j < n, j ≠ i} q j  ≤  q(last) · 1  ≤  1/2
        where the middle inequality is the IH on q restricted to Fin n.
      * Total ≤ 1/2 + 1/2 = 1.
    KEY LEMMAS: Fin.sum_univ_two, Fin.prod_univ_two,
                Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
                NNReal.prod_le_pow_of_le, pow_le_one. -/
theorem sum_prod_erase_le_one'
    {n : ℕ} (hn : n ≥ 2)
    (q : Fin n → NNReal)
    (hq : ∀ i, q i ≤ 1 / 2)
    (hqpos : ∀ i, 0 < q i) :
    ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q j) ≤ 1 := by
  induction n with
  | zero => omega
  | one  => omega
  | succ n ih =>
      by_cases hn2 : n = 1
      · -- Base case: n + 1 = 2
        subst hn2
        simp only [Fin.sum_univ_two, Fin.prod_univ_two]
        -- LHS = (if 0 = 0 then 1 else q 1) * (if 1 = 0 then 1 else q 1)
        --     + (if 0 = 1 then 1 else q 0) * (if 1 = 1 then 1 else q 0)
        -- = 1 * q 1 + q 0 * 1 = q 1 + q 0
        simp only [Fin.isValue, ite_true, ite_false, mul_one, one_mul]
        -- q 1 + q 0 ≤ 1 from hq 0 and hq 1 each ≤ 1/2
        have h0 : q 0 ≤ 1 / 2 := hq 0
        have h1 : q 1 ≤ 1 / 2 := hq 1
        calc q 1 + q 0 ≤ 1 / 2 + 1 / 2 := add_le_add h1 h0
          _ = 1 := by norm_num
      · -- Inductive step
        sorry
        /- DETAILED SKETCH (for Aristotle):
           n + 1 ≥ 3, so n ≥ 2 and the IH applies to n.
           Write Fin (n+1) = Fin n ∪ {Fin.last n} via castSucc/last decomposition.
           Use Fin.sum_univ_castSucc to split the outer sum:
             ∑_{i : Fin (n+1)} ∏_{j} (if j=i then 1 else q j)
             = (∑_{i : Fin n} ∏_{j : Fin (n+1)} (if j.castSucc=i.castSucc then 1 else q j))
               + ∏_{j : Fin n} q j.castSucc
           For the first sum: factor out q (Fin.last n) from each inner product
             (since j = Fin.last n is never equal to i.castSucc),
             giving q(last) · ∑_{i : Fin n} ∏_{j : Fin n} (if j=i then 1 else q j)
             ≤ q(last) · 1  [by IH, since n ≥ 2]
             ≤ 1/2.
           For the second term: ∏_{j : Fin n} q j ≤ (1/2)^n ≤ 1/2.
           Sum ≤ 1/2 + 1/2 = 1. □
        -/

/-! ## Main theorem -/

/-- **Theorem 4 (Sequential ≤ Parallel).** For n ≥ 2 independent subgoals
    with success probabilities each ≤ 1/2, the sum of reciprocals ≤ their product.

    PROVIDED SOLUTION
    Step 1: Rewrite ∏ 1/qᵢ = 1 / ∏ qᵢ using Finset.prod_div_distrib.
    Step 2: After clearing the denominator (∏ qᵢ > 0), the goal becomes
            (∑ 1/qᵢ) · (∏ qᵢ) ≤ 1.
    Step 3: Expand: (∑ᵢ 1/qᵢ) · (∏ⱼ qⱼ) = ∑ᵢ ∏_{j ≠ i} qⱼ.
            This uses ∏ⱼ qⱼ / qᵢ = ∏_{j ≠ i} qⱼ (Finset.prod_erase).
    Step 4: Apply sum_prod_erase_le_one' to conclude ≤ 1.
    KEY LEMMAS: Finset.prod_div_distrib, Finset.prod_erase, Finset.sum_mul,
                NNReal.div_self, sum_prod_erase_le_one'. -/
theorem sequential_le_parallel
    {n : ℕ} (hn : n ≥ 2)
    (q : Fin n → NNReal)
    (hq : ∀ i, q i ≤ 1 / 2)
    (hqpos : ∀ i, 0 < q i) :
    ∑ i, (1 / q i) ≤ ∏ i, (1 / q i) := by
  sorry

/-- **Theorem 4 (strict inequality for q < 1/2).** -/
theorem sequential_lt_parallel
    {n : ℕ} (hn : n ≥ 2)
    (q : Fin n → NNReal)
    (hq : ∀ i, q i < 1 / 2)
    (hqpos : ∀ i, 0 < q i) :
    ∑ i, (1 / q i) < ∏ i, (1 / q i) := by
  sorry

/-- **Corollary:** Sequential decomposition is the optimal search strategy
    for a fixed AND node with n ≥ 2 subgoals. -/
theorem sequential_search_optimal
    (b : ℕ) (hb : b ≥ 2)
    (q : Fin b → NNReal)
    (hq : ∀ i, q i ≤ 1 / 2) (hqpos : ∀ i, 0 < q i) :
    (∑ i, (1 / q i)) ≤ (∏ i, (1 / q i)) :=
  sequential_le_parallel hb q hq hqpos
