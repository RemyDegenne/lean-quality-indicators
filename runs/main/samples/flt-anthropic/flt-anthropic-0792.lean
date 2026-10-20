namespace P2MW.S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section DeskModule03

set_option autoImplicit false

noncomputable section

open Matrix

namespace FLT

namespace PrincipalSeriesGL2Padic

p2m_open

open LocalNewvector

variable (p : ℕ) [Fact p.Prime]

p2m_reactivate

section OtherChart

variable (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

theorem weyl_mul_borelElem_one_one_eq (y : ℚ_[p]) (hy : y ≠ 0) :
    weyl p * borelElem p 1 1 y
      = borelElem p (Units.mk0 (-y⁻¹) (neg_ne_zero.mpr (inv_ne_zero hy))) (Units.mk0 y hy) 1
          * lowerUnip p y⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_weyl, coe_borelElem, coe_borelElem, coe_lowerUnip]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hy]

end OtherChart
end PrincipalSeriesGL2Padic
end FLT
end
end DeskModule03
end P2MW.S_LocalNewvector_PSCarrier_existsUnique_mem_inf_fixedSubmodule_padicK1_one_of_stable
