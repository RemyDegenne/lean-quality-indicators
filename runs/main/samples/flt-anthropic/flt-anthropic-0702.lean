namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot

set_option autoImplicit false

noncomputable section

namespace K1Aux

p2m_open

section general

variable {R : Type*} [CommRing R]

theorem coeff_X_zero_mul_X_one_mul (φ : MvPowerSeries (Fin 2) R) (i j : ℕ) :
    coeff (ij i j) (X 0 * X 1 * φ) = if 1 ≤ i ∧ 1 ≤ j then coeff (ij (i - 1) (j - 1)) φ else 0 := by
  rw [X_zero_mul_X_one, coeff_monomial_mul, ij_sub_ij, one_mul]
  simp only [ij_le_ij_iff]

end general
end K1Aux
end
end P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot
