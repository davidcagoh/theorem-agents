import Mathlib
import AutomatedProofs.Defs

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

    Proof by induction on n.
    Base (n = 2): sum = q 0 + q 1 ≤ 1/2 + 1/2 = 1.
    Step (n+1 ≥ 3): split outer sum at last index via Fin.sum_univ_castSucc.
      - Last term (i = last): ∏_{j : Fin n} q j.castSucc ≤ (1/2)^n ≤ 1/2.
      - First n terms: for each i : Fin n, the product over Fin (n+1) with j=i.castSucc
        factors as (∏_{j≠i} q' j) * q(last).
        Summing: (∑ ∏_{j≠i} q' j) * q(last) ≤ 1 * (1/2) = 1/2 by IH.
      - Total ≤ 1/2 + 1/2 = 1.

    KEY LEMMAS: Fin.sum_univ_two, Fin.prod_univ_two,
                Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
                Finset.prod_le_pow_card, Finset.card_fin, pow_le_one₀. -/
theorem sum_prod_erase_le_one'
    {n : ℕ} (hn : n ≥ 2)
    (q : Fin n → NNReal)
    (hq : ∀ i, q i ≤ 1 / 2)
    (hqpos : ∀ i, 0 < q i) :
    ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q j) ≤ 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn1 : n = 1
      · -- Base case: n + 1 = 2
        subst hn1
        show ∑ i : Fin 2, ∏ j : Fin 2, (if j = i then (1 : NNReal) else q j) ≤ 1
        rw [Fin.sum_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
        -- After unfolding: (1 * q 1) + (q 0 * 1) = q 1 + q 0
        simp only [Fin.isValue, ite_true, ite_false, one_mul, mul_one]
        calc q 1 + q 0 ≤ 1 / 2 + 1 / 2 := add_le_add (hq 1) (hq 0)
          _ = 1 := by norm_num
      · -- Inductive step: n + 1 ≥ 3, so n ≥ 2
        have hn_ge2 : n ≥ 2 := by omega
        let q' : Fin n → NNReal := fun i => q i.castSucc
        have hq'_le : ∀ i, q' i ≤ 1 / 2 := fun i => hq i.castSucc
        have hq'_pos : ∀ i, 0 < q' i := fun i => hqpos i.castSucc
        have ih' : ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q' j) ≤ 1 :=
          ih hn_ge2 q' hq'_le hq'_pos
        rw [Fin.sum_univ_castSucc]
        have hne : ∀ j : Fin n, (j.castSucc : Fin (n + 1)) ≠ Fin.last n :=
          fun j => (Fin.castSucc_lt_last j).ne
        -- Bound the last term
        have hlast_term : ∏ j : Fin (n + 1), (if j = Fin.last n then (1 : NNReal) else q j) ≤ 1 / 2 := by
          rw [Fin.prod_univ_castSucc]
          simp only [ite_true, mul_one]
          simp_rw [hne _, if_false]
          calc ∏ j : Fin n, q j.castSucc
              ≤ (1 / 2) ^ (Finset.univ : Finset (Fin n)).card :=
                  Finset.prod_le_pow_card Finset.univ _ (1 / 2) (fun i _ => hq i.castSucc)
            _ = (1 / 2) ^ n := by rw [Finset.card_fin]
            _ ≤ (1 / 2) ^ 1 := by
                apply pow_le_pow_of_le_one (by norm_num) (by norm_num); omega
            _ = 1 / 2 := pow_one _
        -- Factor each castSucc product
        have hfactor : ∀ i : Fin n,
            ∏ j : Fin (n + 1), (if j = i.castSucc then (1 : NNReal) else q j) =
            (∏ j : Fin n, (if j = i then (1 : NNReal) else q' j)) * q (Fin.last n) := by
          intro i
          rw [Fin.prod_univ_castSucc]
          congr 1
          · apply Finset.prod_congr rfl
            intro j _
            simp only [q']
            by_cases hjei : j = i
            · simp [hjei]
            · have : j.castSucc ≠ i.castSucc := Fin.castSucc_injective _ |>.ne hjei
              simp [hjei, this]
          · have hlast_ne : Fin.last n ≠ i.castSucc :=
              fun h => absurd h.symm (Fin.castSucc_lt_last i).ne
            simp [hlast_ne]
        -- Bound the castSucc sum
        have hcast_sum : ∑ i : Fin n, ∏ j : Fin (n + 1),
            (if j = i.castSucc then (1 : NNReal) else q j) ≤ 1 / 2 := by
          simp_rw [hfactor, ← Finset.sum_mul]
          have hS := ih'
          have hqlast := hq (Fin.last n)
          have hqlast_pos := le_of_lt (hqpos (Fin.last n))
          calc (∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q' j)) * q (Fin.last n)
              ≤ 1 * (1 / 2) := mul_le_mul hS hqlast hqlast_pos (by norm_num)
            _ = 1 / 2 := one_mul _
        calc ∑ i : Fin n, ∏ j : Fin (n + 1), (if j = i.castSucc then (1 : NNReal) else q j) +
              ∏ j : Fin (n + 1), (if j = Fin.last n then (1 : NNReal) else q j)
            ≤ 1 / 2 + 1 / 2 := add_le_add hcast_sum hlast_term
          _ = 1 := by norm_num

/-! ## Main theorem -/

/-
PROBLEM
**Theorem 4 (Sequential ≤ Parallel).** For n ≥ 2 independent subgoals
    with success probabilities each ≤ 1/2, the sum of reciprocals ≤ their product.

    Proof:
    1. ∏ 1/qᵢ = 1 / ∏ qᵢ  (by simp with one_div, Finset.prod_inv_distrib)
    2. Suffices to show (∑ 1/qᵢ) * ∏ qᵢ ≤ 1  (via le_div_iff₀).
    3. (∑ᵢ 1/qᵢ) * ∏ⱼ qⱼ = ∑ᵢ ∏_j (if j=i then 1 else qⱼ).
       Key step: (1/qᵢ) * ∏ qⱼ = ∏_j (if j=i then 1 else qⱼ)
       because ∏ q = (∏_j (if j=i then 1 else q j)) * q i
       via Finset.prod_erase_mul.
    4. Apply sum_prod_erase_le_one'.

    KEY LEMMAS: one_div, Finset.prod_inv_distrib, le_div_iff₀,
                Finset.sum_mul, Finset.prod_erase_mul, sum_prod_erase_le_one'.

PROVIDED SOLUTION
Goal: ∏_j q j = (∏_j (if j=i then 1 else q j)) * q i

Use symm of Finset.prod_erase_mul on q to get: ∏_{j in univ.erase i} q j * q i = ∏_j q j
Then show ∏_j (if j=i then 1 else q j) = ∏_{j in univ.erase i} q j.

Approach:
  rw [← Finset.prod_erase_mul Finset.univ q (Finset.mem_univ i)]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hne]
-/
theorem sequential_le_parallel
    {n : ℕ} (hn : n ≥ 2)
    (q : Fin n → NNReal)
    (hq : ∀ i, q i ≤ 1 / 2)
    (hqpos : ∀ i, 0 < q i) :
    ∑ i, (1 / q i) ≤ ∏ i, (1 / q i) := by
  have hprod_pos : 0 < ∏ i, q i := Finset.prod_pos (fun i _ => hqpos i)
  have hprod_ne : ∏ i, q i ≠ 0 := ne_of_gt hprod_pos
  have hprod_inv : ∏ i : Fin n, (1 / q i) = 1 / ∏ i, q i := by
    simp [one_div, Finset.prod_inv_distrib]
  rw [hprod_inv, le_div_iff₀ hprod_pos]
  -- Goal: (∑ 1/qᵢ) * ∏ qᵢ ≤ 1
  have hexpand : (∑ i : Fin n, 1 / q i) * ∏ i : Fin n, q i =
      ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    have hqi_ne : q i ≠ 0 := ne_of_gt (hqpos i)
    -- (1/qᵢ) * ∏ qⱼ = ∏_j (if j=i then 1 else qⱼ)
    -- Proof: ∏ q = (∏_j (if j=i then 1 else q j)) * q i  by Finset.prod_erase_mul
    -- So (1/qᵢ) * ∏ q = ∏_j (if j=i then 1 else q j)
    have hprod_split : ∏ j : Fin n, q j =
        (∏ j : Fin n, (if j = i then (1 : NNReal) else q j)) * q i := by
      /- PROOF SKETCH FOR ARISTOTLE:
         Goal: ∏_j q j = (∏_j (if j=i then 1 else q j)) * q i
         Step 1: ∏_j (if j=i then 1 else q j) = ∏_{j≠i} q j
           Because the j=i term contributes 1, and j≠i terms contribute q j.
           Use: rw [← Finset.prod_erase_mul Finset.univ (fun j => if j=i then 1 else q j) (Finset.mem_univ i)]
                simp only [ite_true, mul_one]
                apply Finset.prod_congr rfl; intro j hj; simp [Finset.mem_erase.mp hj |>.1]
         Step 2: (∏_{j≠i} q j) * q i = ∏_j q j
           By: Finset.prod_erase_mul Finset.univ q (Finset.mem_univ i)
         KEY LEMMAS: Finset.prod_erase_mul, Finset.mem_erase, Finset.prod_congr -/
      simp +decide [ Finset.prod_ite, Finset.filter_ne', Finset.filter_eq', hqi_ne ];
      rw [ Finset.prod_erase_mul _ _ ( Finset.mem_univ _ ) ]
    rw [one_div, hprod_split, mul_comm (∏ _ : Fin n, _) _, ← mul_assoc,
        inv_mul_cancel₀ hqi_ne, one_mul]
  rw [hexpand]
  exact sum_prod_erase_le_one' hn q hq hqpos

/-
PROBLEM
**Theorem 4 (strict inequality for q < 1/2).**
    When all qᵢ < 1/2 (strict), the inequality is strict.

    Proof: use sequential_le_parallel for ≤, then show ≠ by contradiction.
    If ∑ 1/qᵢ = ∏ 1/qᵢ, then (∑ 1/qᵢ) * ∏ qᵢ = 1.
    But LHS = ∑ᵢ ∏_{j≠i} qⱼ < 1 since each qᵢ < 1/2 strictly.

    KEY LEMMAS: lt_of_le_of_ne, ne_of_lt, add_lt_add.

PROVIDED SOLUTION
We have hsum_times_prod : (∑ 1/qᵢ) * ∏ qᵢ = 1.

Step 1: Show (∑ 1/qᵢ) * ∏ qᵢ = ∑ᵢ ∏_j (if j=i then 1 else qⱼ), same expansion as in sequential_le_parallel.

Step 2: Prove sum_prod_erase_lt_one: ∑ᵢ ∏_j (if j=i then 1 else qⱼ) < 1, by the same induction as sum_prod_erase_le_one' but using strict inequalities since each q i < 1/2.
  Base (n=2): q 1 + q 0 < 1/2 + 1/2 = 1 by add_lt_add.
  Inductive step: same structure but use strict inequality on at least one side of the addition. The cast_sum part: (∑ erased prods) * q(last) ≤ 1 * q(last) < 1 * (1/2) = 1/2 since ih gives ≤ 1 and q(last) < 1/2. The last_term: ∏ q j.castSucc ≤ (1/2)^n ≤ 1/2 (non-strict suffices). Total < 1/2 + 1/2 = 1 since one summand is strict.

Step 3: From steps 1 and 2, we get (∑ 1/qᵢ) * ∏ qᵢ < 1, contradicting hsum_times_prod via exact absurd hsum_times_prod (ne_of_lt h).

Key: prove the strict version as a local have, do the expansion as a local have, combine for contradiction.
-/
theorem sequential_lt_parallel
    {n : ℕ} (hn : n ≥ 2)
    (q : Fin n → NNReal)
    (hq : ∀ i, q i < 1 / 2)
    (hqpos : ∀ i, 0 < q i) :
    ∑ i, (1 / q i) < ∏ i, (1 / q i) := by
  apply lt_of_le_of_ne
  · exact sequential_le_parallel hn q (fun i => le_of_lt (hq i)) hqpos
  · intro heq
    have hprod_pos : 0 < ∏ i, q i := Finset.prod_pos (fun i _ => hqpos i)
    have hprod_ne : ∏ i, q i ≠ 0 := ne_of_gt hprod_pos
    have hprod_inv : ∏ i : Fin n, (1 / q i) = 1 / ∏ i, q i := by
      simp [one_div, Finset.prod_inv_distrib]
    have hsum_times_prod : (∑ i : Fin n, 1 / q i) * ∏ i : Fin n, q i = 1 := by
      have h1 : ∑ i : Fin n, 1 / q i = 1 / ∏ i, q i := by rw [← hprod_inv]; exact heq
      rw [h1, div_mul_cancel₀ 1 hprod_ne]
    have hprod_lt : (∑ i, (1 / q i)) * (∏ i, q i) < 1 := by
      -- By definition of success probability, we have:
      have h_def : (∑ i : Fin n, 1 / q i) * (∏ i : Fin n, q i) = ∑ i : Fin n, ∏ j : Fin n, if j = i then (1 : NNReal) else q j := by
        simp +decide [ Finset.sum_mul _ _ _, Finset.prod_ite, Finset.filter_ne', Finset.filter_eq' ];
        exact Finset.sum_congr rfl fun i hi => by rw [ inv_mul_eq_div, ← Finset.prod_erase_mul _ _ hi, mul_div_cancel_right₀ _ ( ne_of_gt ( hqpos i ) ) ] ;
      have hsum_lt_one : ∀ (n : ℕ) (hn : n ≥ 2) (q : Fin n → NNReal), (∀ i, q i < 1 / 2) → (∀ i, 0 < q i) → ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q j) < 1 := by
        intros n hn q hq hqpos
        induction' n, Nat.succ_le_iff.mpr hn using Nat.le_induction with n hn ih;
        · simp +decide [ Fin.sum_univ_two, Fin.prod_univ_two ];
          convert add_lt_add ( hq 1 ) ( hq 0 ) using 1 ; ring;
        · -- Split the sum into the last term and the sum over the first n terms.
          have h_split : ∑ i : Fin (n + 1), ∏ j : Fin (n + 1), (if j = i then (1 : NNReal) else q j) = (∏ j : Fin n, q (Fin.castSucc j)) + q (Fin.last n) * ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q (Fin.castSucc j)) := by
            simp +decide [ Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, Finset.prod_erase ];
            simp +decide [ Fin.ext_iff, Finset.mul_sum _ _ _, mul_comm, add_comm ];
            exact Finset.sum_congr rfl fun i hi => by rw [ if_neg ( by linarith [ Fin.is_lt i ] ) ] ;
          have h_prod_lt_half : ∏ j : Fin n, q (Fin.castSucc j) < (1 / 2) ^ n := by
            have h_prod_lt_half : ∏ j : Fin n, q (Fin.castSucc j) < ∏ j : Fin n, (1 / 2 : NNReal) := by
              apply_rules [ Finset.prod_lt_prod ] <;> norm_num;
              · exact fun i => hqpos _;
              · exact fun i => le_of_lt ( hq _ );
              · exact ⟨ ⟨ 0, by linarith ⟩, hq _ ⟩;
            simpa using h_prod_lt_half;
          have h_sum_lt_one : ∑ i : Fin n, ∏ j : Fin n, (if j = i then (1 : NNReal) else q (Fin.castSucc j)) < 1 := by
            exact ih ‹_› _ ( fun i => hq _ ) ( fun i => hqpos _ );
          have h_final : (1 / 2 : NNReal) ^ n + (1 / 2 : NNReal) * 1 ≤ 1 := by
            rcases n with ( _ | _ | n ) <;> norm_num [ pow_succ' ] at *;
            rw [ ← NNReal.coe_le_coe ] ; norm_num ; ring ; norm_num [ pow_succ' ] ; nlinarith [ pow_le_pow_of_le_one ( by norm_num : ( 0 : ℝ ) ≤ 1 / 2 ) ( by norm_num ) ( show n ≥ 0 by norm_num ) ] ;
          exact h_split.symm ▸ lt_of_lt_of_le ( add_lt_add_of_lt_of_le h_prod_lt_half ( mul_le_mul' ( le_of_lt ( hq _ ) ) h_sum_lt_one.le ) ) ( by simpa using h_final );
      exact h_def.symm ▸ hsum_lt_one n hn q hq hqpos
    exact hprod_lt.ne hsum_times_prod;

/- PROOF SKETCH FOR ARISTOTLE:
       We have hsum_times_prod : (∑ 1/qᵢ) * ∏ qᵢ = 1.
       From hexpand: (∑ 1/qᵢ) * ∏ qᵢ = ∑ᵢ ∏_j (if j=i then 1 else qⱼ).
       Since each qᵢ < 1/2 (strict), prove ∑ᵢ ∏_j (if j=i then 1 else qⱼ) < 1.
       Proof by same induction as sum_prod_erase_le_one' but strict:
       Base (n=2): q0 + q1 < 1/2 + 1/2 = 1 via add_lt_add (hq 0) (hq 1).
       Step: q(last) * ∑ < (1/2) * 1 = 1/2 (strict since q(last) < 1/2)
             and ∏ q j.castSucc < (1/2)^n < 1/2 (strict since each q j < 1/2).
             Total < 1/2 + 1/2 = 1.
       This contradicts hsum_times_prod = 1 via exact absurd hsum_times_prod (ne_of_lt h).
       KEY LEMMAS: add_lt_add, mul_lt_one_of_nonneg_of_lt_one_left,
                   Finset.prod_lt_pow_card, ne_of_lt. -/

/-- **Corollary:** Sequential decomposition is the optimal search strategy
    for a fixed AND node with n ≥ 2 subgoals. -/
theorem sequential_search_optimal
    (b : ℕ) (hb : b ≥ 2)
    (q : Fin b → NNReal)
    (hq : ∀ i, q i ≤ 1 / 2) (hqpos : ∀ i, 0 < q i) :
    (∑ i, (1 / q i)) ≤ (∏ i, (1 / q i)) :=
  sequential_le_parallel hb q hq hqpos