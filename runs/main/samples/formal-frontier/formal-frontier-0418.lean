@[expose] public section

open scoped TensorProduct

namespace TensorProduct

@[simp]
theorem tmul_rationalAngle_eq_zero (c q : ℚ) :
    c ⊗ₜ[ℤ] AddCircle.rationalAngle q = 0 := by
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Rat.den_ne_zero q)
  have hcoeff : (q.den : ℤ) • (c / (q.den : ℚ)) = c := by
    rw [zsmul_eq_mul, Int.cast_natCast, mul_div_cancel₀ c hden]
  calc
    c ⊗ₜ[ℤ] AddCircle.rationalAngle q =
        ((q.den : ℤ) • (c / (q.den : ℚ))) ⊗ₜ[ℤ] AddCircle.rationalAngle q := by
          rw [hcoeff]
    _ = (c / (q.den : ℚ)) ⊗ₜ[ℤ] ((q.den : ℤ) • AddCircle.rationalAngle q) :=
      TensorProduct.smul_tmul (q.den : ℤ) (c / (q.den : ℚ)) (AddCircle.rationalAngle q)
    _ = 0 := by rw [AddCircle.den_zsmul_rationalAngle, TensorProduct.tmul_zero]

end TensorProduct
end
