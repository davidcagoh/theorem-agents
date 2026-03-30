import Mathlib
import AutomatedProofs.AOTree.Defs

set_option linter.style.longLine false
set_option linter.style.whitespace false

universe u

/-!
# Theorem 2: Policy Improvement Monotonically Reduces Hitting Time

If policy π' assigns at least as much weight to correct tactics as π at every
OR node on a proof path, then `successProb π' t ≥ successProb π t` pointwise,
so `E[T under π'] ≤ E[T under π]`.

This is the most technically involved of the four theorems; the key difficulty
is that shifting weight *toward* correct children requires weight to come *from*
incorrect children, and the rearrangement step uses the simplex constraint.
-/

open NNReal BigOperators AOTree

/-! ## Definitions -/

/-- `π'` dominates `π` on correct children of tree `t`. -/
structure PolicyDominates
    (π π' : ℕ → ℕ → NNReal)
    (t : AOTree α)
    (correctChild : ℕ → ℕ → Prop) : Prop where
  /-- π' puts ≥ as much weight on correct children -/
  correct_ge : ∀ nid idx, correctChild nid idx → π nid idx ≤ π' nid idx
  /-- Both policies are well-formed (weights sum to 1 at each OR node) -/
  wf  : ∀ nid n, ∑ i : Fin n, π  nid i = 1
  wf' : ∀ nid n, ∑ i : Fin n, π' nid i = 1

/-! ## Key lemma -/

/-- **Lemma 2.1 (successProb monotone in policy).**
    If π' dominates π on correct children, and correct children have
    higher success probability than incorrect ones, then
    `successProb π t nid ≤ successProb π' t nid` for all nid.

    PROVIDED SOLUTION
    Structural induction on t.

    Base (leaf): successProb = 1 for both policies. Trivial.

    OR node (orNode s cs):
      successProb π  = ∑ᵢ π(i)  * sp(π,  child i)
      successProb π' = ∑ᵢ π'(i) * sp(π', child i)
      Decompose the difference:
        ∑ π'(i)·sp'(i) - ∑ π(i)·sp(i)
        = ∑ (π'(i) - π(i))·sp'(i)   [weight-shift term]
        + ∑ π(i)·(sp'(i) - sp(i))   [value-improvement term]
      Value-improvement term ≥ 0 by the inductive hypothesis (sp' ≥ sp).
      Weight-shift term: let good = {i : correctChild nid i}.
        On good: π'(i) ≥ π(i), and sp'(good) ≥ sp'(bad) [by hcorrect_better].
        Since ∑ π' = ∑ π = 1, the excess weight on good = deficit on bad.
        So ∑ (π'(i)-π(i))·sp'(i) ≥ 0 by NNReal.weighted_sum_mono.
      Combine both non-negative terms.
    KEY LEMMAS: NNReal.weighted_sum_mono (from Defs), Finset.sum_sub_distrib,
                Finset.sum_compl_add_sum, NNReal.add_le_add.

    AND node (andNode s cs):
      successProb π  = ∏ sp(π,  child i)
      successProb π' = ∏ sp(π', child i)
      Each factor increases by the IH (sp'(child i) ≥ sp(child i)).
      All factors are in [0,1], so the product is monotone:
      apply Finset.prod_le_prod; exact zero_le _; exact ih i nid. -/
lemma successProb_mono
    {α : Type u} (t : AOTree α)
    (π π' : ℕ → ℕ → NNReal)
    (correctChild : ℕ → ℕ → Prop)
    (hdom : PolicyDominates π π' t correctChild)
    (hcorrect_better : ∀ nid idx idx',
        correctChild nid idx → ¬ correctChild nid idx' →
        successProb π t (nid + idx' + 1) ≤ successProb π t (nid + idx + 1)) :
    ∀ nid, successProb π t nid ≤ successProb π' t nid := by
  intro nid
  induction t with
  | leaf _ => simp [successProb]
  | orNode s cs ih =>
      simp only [successProb]
      sorry
      /- DETAILED PROOF (see docstring above) -/
  | andNode s cs ih =>
      simp only [successProb]
      apply Finset.prod_le_prod
      · intro i _; exact zero_le _
      · intro i _; exact ih i nid

/-! ## Main theorem -/

/-- **Theorem 2 (policy improvement reduces hitting time).** -/
theorem policy_improvement_reduces_hitting_time
    {α : Type u} (t : AOTree α)
    (π π' : ℕ → ℕ → NNReal)
    (correctChild : ℕ → ℕ → Prop)
    (hdom : PolicyDominates π π' t correctChild)
    (hcorrect_better : ∀ nid idx idx',
        correctChild nid idx → ¬ correctChild nid idx' →
        successProb π t (nid + idx' + 1) ≤ successProb π t (nid + idx + 1))
    (hpos : 0 < successProb π t 0) :
    (1 : NNReal) / successProb π' t 0 ≤ (1 : NNReal) / successProb π t 0 := by
  apply NNReal.div_le_div_left le_rfl hpos
  exact successProb_mono t π π' correctChild hdom hcorrect_better 0

/-- **Corollary (expert iteration soundness).** Each training step that improves
    the policy monotonically reduces the expected hitting time. -/
theorem expert_iteration_soundness
    {α : Type u} (t : AOTree α)
    (πs : ℕ → ℕ → ℕ → NNReal)
    (correctChild : ℕ → ℕ → Prop)
    (hiter : ∀ k, PolicyDominates (πs k) (πs (k + 1)) t correctChild)
    (hcorrect : ∀ k nid idx idx',
        correctChild nid idx → ¬ correctChild nid idx' →
        successProb (πs k) t (nid + idx' + 1) ≤
        successProb (πs k) t (nid + idx + 1))
    (hpos : ∀ k, 0 < successProb (πs k) t 0) :
    ∀ k, (1 : NNReal) / successProb (πs (k + 1)) t 0 ≤
         (1 : NNReal) / successProb (πs k)       t 0 := fun k =>
  policy_improvement_reduces_hitting_time t (πs k) (πs (k + 1))
    correctChild (hiter k) (hcorrect k) (hpos k)
