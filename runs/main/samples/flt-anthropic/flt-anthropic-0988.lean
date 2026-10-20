namespace P2MW.S_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial

set_option autoImplicit false

noncomputable section

open Polynomial

namespace P2mNormFormQ

section PolyP

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem coeff_vec_X_sub_C (c : R) :
    (fun i : Fin 1 => (X - C c).coeff (i : ℕ)) = fun _ => -c := by
  funext i
  fin_cases i
  simp [coeff_X]

end PolyP
end P2mNormFormQ
end
end P2MW.S_Polynomial_exists_monic_eq_resultant_of_mul_of_forall_exists_mvPolynomial
