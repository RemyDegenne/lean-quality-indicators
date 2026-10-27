@[expose] public section

noncomputable section

open GeneralLinearCoordinateRing

open scoped TensorProduct

universe u

namespace SpecialLinearCoordinateRing

variable (K : Type u) [CommRing K] (n : Type u) [Fintype n] [DecidableEq n]

/-- The canonical map from the Hopf quotient to the polynomial presentation. -/
def coordinateRingToPolynomialQuotient :
    CoordinateRing K n →ₐ[K] PolynomialCoordinateRing K n :=
  Ideal.Quotient.liftₐ (determinantOneIdeal K n)
    (localizationToPolynomialQuotient K n) (by
      intro element membership
      obtain ⟨multiplier, hmultiplier⟩ := Ideal.mem_span_singleton'.mp membership
      rw [← hmultiplier, map_mul, map_sub, map_one]
      have hdet : localizationToPolynomialQuotient K n (matrix K n).det = 1 := by
        rw [matrix_det]
        simp only [localizationToPolynomialQuotient,
          IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
        exact polynomialQuotient_det K n
      rw [hdet, sub_self, mul_zero])

end SpecialLinearCoordinateRing
end
end
