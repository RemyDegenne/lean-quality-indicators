namespace P2MW.S_RubinSilverberg_exists_polynomial_rsFamily

set_option autoImplicit false

open Polynomial

namespace M4cP2

namespace D52

section EvalZ

theorem PhiA_eq (j : ℕ) (hj : j < 21) : PhiPlusA j = PhiMinusA j := by
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun i : Fin 197 => ((i : ℕ) : ℤ))
    (fun a b h => Fin.ext (by simpa using h)) (fun i => eval_PhiA j i hj i.isLt) ?_
  simpa using Nat.lt_succ_of_le (natDegree_PhiA_le j)

end EvalZ
end D52
end M4cP2
end P2MW.S_RubinSilverberg_exists_polynomial_rsFamily
