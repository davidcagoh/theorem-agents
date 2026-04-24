import Mathlib
import AutomatedProofs.AOTree.Defs
import AutomatedProofs.AOTree.Theorem4

set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

/-!
# Theorem 4 (strong form): Sharp regime for sequential ≤ parallel

The original `sequential_le_parallel` requires `q(i) ≤ 1/2` for every `i`. The sharp
threshold is `∑ q(i) ≤ 1` — strictly weaker than uniform `q(i) ≤ 1/2`.
-/

open NNReal BigOperators AOTree

/-! ## Helper lemmas -/

/-
Each component ≤ 1 when the sum is ≤ 1 (for NNReal).
-/
private lemma each_le_one_of_sum_le_one
    {n : ℕ} (q : Fin n → NNReal)
    (hsum : (∑ i, q i) ≤ 1)
    (i : Fin n) : q i ≤ 1 := by
  exact le_trans ( Finset.single_le_sum ( fun a _ => zero_le ( q a ) ) ( Finset.mem_univ i ) ) hsum

/-
For n ≥ 2 NNReals each ≤ 1, their product is ≤ their sum.
    Proof: ∏ qᵢ ≤ q₀ (since other factors ≤ 1) ≤ ∑ qᵢ (since all nonneg).
-/
private lemma prod_le_sum_of_le_one
    {n : ℕ} (hn : n ≥ 2) (q : Fin n → NNReal) (hq : ∀ i, q i ≤ 1) :
    ∏ i, q i ≤ ∑ i, q i := by
  rcases n with ( _ | _ | n ) <;> norm_num at *;
  rw [ Fin.sum_univ_succ, Fin.prod_univ_succ ];
  exact le_add_of_le_of_nonneg ( mul_le_of_le_one_right' ( Finset.prod_le_one' fun _ _ => hq _ ) ) ( NNReal.zero_le_coe )

/-! ## Main lemma -/

/-
**Lemma 4.1 (strong).** Under `∑ q_i ≤ 1`, the sum of products-with-one-erased
    is ≤ 1.

    Proof by induction on n:
    - Base (n = 2): ∑ = q₁ + q₀ = ∑ qᵢ ≤ 1.
    - Step (n+1, n ≥ 2): Split via Fin.sum_univ_castSucc.
      Let q' = q ∘ castSucc. Since ∑ q'ᵢ ≤ 1 - q_last ≤ 1, IH gives
      ∑ₖ ∏_{j≠k} q'_j ≤ 1.
      - castSucc terms: each factors as (∏_{j≠k} q'_j) * q_last.
        Sum = q_last * (∑ₖ ∏_{j≠k} q'_j) ≤ q_last * 1 = q_last.
      - last term: ∏ q'_j ≤ ∑ q'_j by prod_le_sum_of_le_one (n ≥ 2, each q'_j ≤ 1).
      - Total ≤ q_last + ∑ q'_j = ∑ qᵢ ≤ 1.
-/
lemma sum_prod_erase_le_one_of_sum_le_one
    {n : ℕ} (hn : n ≥ 2) (q : Fin n → NNReal)
    (hsum : (∑ i, q i) ≤ 1) :
    ∑ i, (∏ j ∈ Finset.univ.erase i, q j) ≤ 1 := by
  induction' n, hn using Nat.le_induction with n hn ih;
  · simp_all +decide [ Fin.univ_succ ];
    simp_all +decide [ add_comm, Finset.prod ];
  · -- Split the sum into the last term and the rest.
    have h_split : ∑ i : Fin (n + 1), ∏ j ∈ Finset.univ.erase i, q j = q (Fin.last n) * ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, q (Fin.castSucc j) + ∏ j : Fin n, q (Fin.castSucc j) := by
      rw [ Fin.sum_univ_castSucc, Finset.mul_sum _ _ _ ];
      refine' congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun i hi => _ ) _;
      · rw [ show ( Finset.univ.erase ( Fin.castSucc i ) : Finset ( Fin ( n + 1 ) ) ) = Finset.image ( Fin.castSucc ) ( Finset.univ.erase i ) ∪ { Fin.last n } from ?_, Finset.prod_union ] <;> norm_num;
        · ring;
        · ext j ; by_cases hj : j = Fin.last n <;> simp +decide [ hj, Fin.ext_iff ];
          · linarith [ Fin.is_lt i ];
          · exact ⟨ fun h => ⟨ ⟨ j, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hj ) ⟩, h, rfl ⟩, fun ⟨ a, ha, ha' ⟩ => by simpa [ Fin.ext_iff, ha' ] using ha ⟩;
      · refine' Finset.prod_bij ( fun j hj => ⟨ j, by
          exact lt_of_le_of_ne ( Nat.le_of_lt_succ j.2 ) ( by simpa [ Fin.ext_iff ] using Finset.ne_of_mem_erase hj ) ⟩ ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
        exact fun i => ⟨ ⟨ i, by linarith [ Fin.is_lt i ] ⟩, by linarith [ Fin.is_lt i ], rfl ⟩;
    -- Apply the induction hypothesis to the sum of the products with one element erased.
    have h_ind : ∑ i : Fin n, ∏ j ∈ Finset.univ.erase i, q (Fin.castSucc j) ≤ 1 := by
      apply ih;
      exact le_trans ( by rw [ Fin.sum_univ_castSucc ] ; exact le_add_of_nonneg_right <| by positivity ) hsum;
    have h_prod_le_sum : ∏ j : Fin n, q (Fin.castSucc j) ≤ ∑ j : Fin n, q (Fin.castSucc j) := by
      apply_rules [ prod_le_sum_of_le_one ];
      exact fun i => le_trans ( Finset.single_le_sum ( fun a _ => zero_le ( q a ) ) ( Finset.mem_univ _ ) ) hsum;
    simp_all +decide [ Fin.sum_univ_castSucc ];
    exact le_trans ( add_le_add ( mul_le_of_le_one_right' h_ind ) h_prod_le_sum ) ( by simpa [ add_comm ] using hsum )

/-! ## Main theorem -/

/-
**Theorem 4 (strong).** Sequential ≤ parallel under the sharp condition
    `∑ q(i) ≤ 1`.

    Proof mirrors `sequential_le_parallel` from Theorem4.lean:
    1. ∏ 1/qᵢ = 1 / ∏ qᵢ
    2. Suffices (∑ 1/qᵢ) * ∏ qᵢ ≤ 1
    3. (∑ 1/qᵢ) * ∏ qᵢ = ∑ᵢ ∏_{j≠i} qⱼ (via Finset.prod_erase_mul)
    4. Apply sum_prod_erase_le_one_of_sum_le_one.
-/
theorem sequential_le_parallel_sharp
    {n : ℕ} (hn : n ≥ 2) (q : Fin n → NNReal)
    (hqpos : ∀ i, 0 < q i)
    (hsum : (∑ i, q i) ≤ 1) :
    ∑ i, (1 / q i) ≤ ∏ i, (1 / q i) := by
  -- Use the identity $\sum_{i=1}^n \frac{1}{q_i} = \frac{\sum_{i=1}^n \prod_{j \neq i} q_j}{\prod_{i=1}^n q_i}$.
  have h_identity : (∑ i, (1 / q i : NNReal)) = (∑ i, (∏ j ∈ Finset.univ.erase i, q j) : NNReal) / (∏ i, q i) := by
    rw [ Finset.sum_div _ _ _ ];
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ ← Finset.prod_erase_mul _ _ hi, div_mul_eq_div_div, div_self <| ne_of_gt <| Finset.prod_pos fun _ _ => hqpos _ ];
  simp_all +decide [ Finset.prod_inv_distrib ];
  exact mul_le_of_le_one_left ( inv_nonneg.mpr ( Finset.prod_nonneg fun _ _ => le_of_lt ( hqpos _ ) ) ) ( sum_prod_erase_le_one_of_sum_le_one hn q hsum )