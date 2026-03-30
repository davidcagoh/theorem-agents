import Mathlib
open NNReal

-- Test: what is the right lemma for 1/a ≤ 1/b when 0 < b ≤ a?
-- i.e. if sp' ≥ sp > 0, then 1/sp' ≤ 1/sp
example (a b : NNReal) (hb : 0 < b) (hab : b ≤ a) : 1 / a ≤ 1 / b := by
  apply div_le_div_of_nonneg_left _ (lt_of_lt_of_le hb hab) hb
  · exact le_refl 1
