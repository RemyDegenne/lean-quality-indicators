namespace P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one

set_option autoImplicit false

open Polynomial Finset

namespace DeligneSerreL49G

section MvEval

variable {σ : Type*}

noncomputable def spec [DecidableEq σ] (i : σ) (t : ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval fun j => if j = i then (Polynomial.X : ℂ[X]) else Polynomial.C t

end MvEval
end DeligneSerreL49G
end P2MW.S_DeligneSerre_eq_of_finite_eulerProduct_functionalEquation_of_norm_coeff_two_eq_one
