@[expose] public section

open Polynomial

open scoped ArithmeticFunction.Moebius

namespace QuadraticIterates

section

variable (a : ℤ)

theorem section1_equiv (ha : ¬IsSquare (-a : ℚ)) (n : ℕ) :
    [Nonempty (GaloisGroup a n ≃* WreathPower n),
     TwoIndependent (fun i : Fin n ↦ (cSeq a ((i : ℕ) + 1) : ℚ)),
     TwoIndependent (fun i : Fin n ↦ (bSeq a ((i : ℕ) + 1) : ℚ))].TFAE := by
  tfae_have 1 ↔ 2 := section1_a_iff_b a ha n
  tfae_have 2 ↔ 3 := section1_b_iff_c a ha n
  tfae_finish

end
end QuadraticIterates
end
