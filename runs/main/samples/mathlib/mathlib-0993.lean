@[expose] public section

universe u v w

local notation "tsze" => TrivSqZeroExt

open scoped RightActions

namespace TrivSqZeroExt

open MulOpposite

section DivisionSemiring

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

protected theorem inv_inv {x : tsze R M} (hx : fst x ≠ 0) : x⁻¹⁻¹ = x :=
  -- adapted from `Matrix.nonsing_inv_nonsing_inv`
  calc
    x⁻¹⁻¹ = 1 * x⁻¹⁻¹ := by rw [one_mul]
    _ = x * x⁻¹ * x⁻¹⁻¹ := by rw [TrivSqZeroExt.mul_inv_cancel hx]
    _ = x := by
      rw [mul_assoc, TrivSqZeroExt.mul_inv_cancel, mul_one]
      rw [fst_inv]
      apply inv_ne_zero hx

end DivisionSemiring
end TrivSqZeroExt
end
