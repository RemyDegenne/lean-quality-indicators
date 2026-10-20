public section

open Polynomial

namespace Polynomial

section NoZeroDivisors

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

theorem irreducible_X_pow_five_add_C_mul_X_add_C {c d : R}
    (hroot : ∀ x : R, x ^ 5 + c * x + d ≠ 0)
    (hquad : ∀ a b : R,
      ¬ (a ^ 4 - 3 * a ^ 2 * b + b ^ 2 + c = 0 ∧ a ^ 3 * b - 2 * a * b ^ 2 + d = 0)) :
    Irreducible (X ^ 5 + C c * X + C d : R[X]) := by
  nontriviality R
  have hdeg : (X ^ 5 + C c * X + C d : R[X]).natDegree = 5 := by compute_degree!
  refine Monic.irreducible_of_degree_le_five_of_not_isRoot_of_not_quadratic_dvd (by monicity!)
    (by rw [hdeg]; decide) (fun x => by simpa using hroot x) fun a b => ?_
  rw [X_sq_add_C_mul_X_add_C_dvd_X_pow_five_add_iff]
  exact hquad a b

end NoZeroDivisors
end Polynomial
end
