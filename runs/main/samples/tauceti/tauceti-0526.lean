public section

open Polynomial NumberField

open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

theorem minpoly_two_mul_sub_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1) :
    minpoly ℤ (2 * θ - 1) = X ^ 2 - C 5 := by
  have h := minpoly_two_mul_sub_one_of_minpoly_eq_X_sq_sub_X_add (minpoly_eq_X_sq_sub_X_add hmin)
  norm_num at h
  exact h

end TauCeti.NumberField.Sqrt5
end
