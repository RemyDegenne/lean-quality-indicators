namespace P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA

set_option autoImplicit false

p2m_open

namespace ModularCurve

p2m_open

namespace ARails

open Complex

open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

theorem coeff_prod_eq (m : ℕ) (s : Finset ℕ) (hs : Finset.range (m + 1) ⊆ s) :
    PowerSeries.coeff m (∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) =
      PowerSeries.coeff m (∏ n ∈ Finset.range (m + 1), ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) := by
  rw [← Finset.prod_sdiff hs, mul_comm]
  apply coeff_mul_of_cong
  apply Cong.prod
  intro n hn
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  exact Cong.one_sub_X_pow (by omega)

end ARails
end ModularCurve
end P2MW.S_ModularForm_E4_mul_eta_pow_eight_eq
