namespace P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit

set_option autoImplicit false

noncomputable section

open Polynomial

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve

p2m_open

namespace UnitConj

section IntegralCoeffs

variable {K : Type*} [Field K]

theorem CoeffsIntegral.mul {f g : LaurentSeries K} (hf : CoeffsIntegral f)
    (hg : CoeffsIntegral g) : CoeffsIntegral (f * g) := by
  intro m
  rw [HahnSeries.coeff_mul]
  exact Subalgebra.sum_mem _ fun ij _ => Subalgebra.mul_mem _ (hf ij.1) (hg ij.2)

end IntegralCoeffs
end UnitConj
end ModularCurve
end
end
end P2MW.S_ModularCurve_exists_monic_rat_relation_int_coeff_modularUnit
