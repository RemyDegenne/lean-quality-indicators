public section

namespace CFSG.GH74.Uniqueness.Bender.Frame

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {E : Type} [Field E]

section LinearAlgebra

open Module

theorem pow_three_eq_one_of_mul_eq_smul {x y : GL (Fin 3) E} {μ : E} (hμ : μ ≠ 1)
    (hxy : (x : Matrix (Fin 3) (Fin 3) E) * y = μ • ((y : Matrix (Fin 3) (Fin 3) E) * x))
    (hdet : (y : Matrix (Fin 3) (Fin 3) E).det = 1) : (y : Matrix (Fin 3) (Fin 3) E) ^ 3 = 1 := by
  set X := (x : Matrix (Fin 3) (Fin 3) E) with hX
  set Y := (y : Matrix (Fin 3) (Fin 3) E) with hY
  set X' := ((x⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) with hX'
  set Y' := ((y⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) with hY'
  have hXX' : X * X' = 1 := by rw [hX, hX', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hYY' : Y * Y' = 1 := by rw [hY, hY', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hY'Y : Y' * Y = 1 := by rw [hY, hY', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have htr : Y.trace = 0 := by
    have h1 : X * Y * X' = μ • Y := by rw [hxy, smul_mul_assoc, mul_assoc, hXX', mul_one]
    have h2 := Matrix.trace_units_conj x Y
    rw [← hX, ← hX', h1, Matrix.trace_smul, smul_eq_mul] at h2
    exact eq_zero_of_eq_mul_of_ne_one hμ h2.symm
  have htr' : Y'.trace = 0 := by
    have h1 : Y' * X = μ • (X * Y') := by
      calc Y' * X = Y' * (X * Y) * Y' := by rw [mul_assoc, mul_assoc, hYY', mul_one]
        _ = μ • (X * Y') := by
          rw [hxy, mul_smul_comm, smul_mul_assoc, ← mul_assoc, hY'Y, one_mul]
    have h2 : Y' = μ • (X * Y' * X') := by
      calc Y' = Y' * X * X' := by rw [mul_assoc, hXX', mul_one]
        _ = μ • (X * Y' * X') := by rw [h1, smul_mul_assoc]
    have h3 := Matrix.trace_units_conj x Y'
    rw [← hX, ← hX'] at h3
    have h4 : Y'.trace = μ * Y'.trace := by
      conv_lhs => rw [h2]
      rw [Matrix.trace_smul, smul_eq_mul, h3]
    exact eq_zero_of_eq_mul_of_ne_one hμ h4
  have hadj : Y.adjugate = Y' := by
    rw [hY', Matrix.coe_units_inv, Matrix.inv_def, ← hY, hdet, Ring.inverse_one, one_smul]
  rw [pow_three_eq_trace_smul_sub, htr, hadj, htr', hdet, zero_smul, zero_smul, sub_zero,
    zero_add, one_smul]

end LinearAlgebra
end CFSG.GH74.Uniqueness.Bender.Frame
end
