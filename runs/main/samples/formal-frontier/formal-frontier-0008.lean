set_option warningAsError true

@[expose] public section

open scoped Matrix

namespace Matrix

universe u

theorem coefficientRowCompletionTwo_inv_mul (R : Type u) [CommRing R]
    (a b : Fin 2 → R) (h : a 0 * b 0 + a 1 * b 1 = 1) :
    (↑((coefficientRowCompletionTwo R a b h)⁻¹) : Matrix (Fin 2) (Fin 2) R) *
      (coefficientRowCompletionTwo R a b h : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp only [← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one]

end Matrix
end
