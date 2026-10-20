namespace P2MW.S_ModularCurve_B3_b3_specialisationEquivariance

set_option autoImplicit false

open scoped Classical

noncomputable section

p2m_open

namespace ModularCurve

namespace B3

p2m_open

open ModularCurve.TatePoint

scoped instance instCharZeroH : CharZero H :=
  charZero_of_injective_algebraMap (algebraMap Qbar H).injective

local notation "ι" => (HahnSeries.ofPowerSeries ℚ Qbar)

theorem goodModel_zero_eq : goodModel 0 =
    ⟨0, 0, 0,
      HahnSeries.single (1 / 3 : ℚ) 1 *
        ι (PowerSeries.C (-1 / 48 : Qbar) * (PowerSeries.X - PowerSeries.C 1728) ^ 3),
      ι (PowerSeries.C (1 / 864 : Qbar) * (PowerSeries.X - PowerSeries.C 1728) ^ 5)⟩ := by
  have hA : jNear 0 - 1728 = HahnSeries.single 1 1 - 1728 := by rw [jNear_zero]
  have h4 : HahnSeries.single (-(2 / 12 : ℚ)) (1 : Qbar) ^ 4 * HahnSeries.single 1 1 =
      HahnSeries.single (1 / 3 : ℚ) 1 := by
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single]; congr 1 <;> norm_num
  have h6 : HahnSeries.single (-(2 / 12 : ℚ)) (1 : Qbar) ^ 6 * HahnSeries.single 1 1 = 1 := by
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single, ← HahnSeries.single_zero_one]
    congr 1 <;> norm_num
  rw [goodModel, scaleVC_zero, nearCurve_eq_ofJNe0Or1728, variableChange_def]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · simp only [WeierstrassCurve.ofJNe0Or1728, hA, val_inv_sU]
    ring
  · simp only [WeierstrassCurve.ofJNe0Or1728, hA, val_inv_sU]
    ring
  · simp only [WeierstrassCurve.ofJNe0Or1728, hA, val_inv_sU]
    ring
  · simp only [WeierstrassCurve.ofJNe0Or1728, hA, val_inv_sU, map_mul, map_pow, map_sub, map_neg,
      map_div₀, map_one, map_ofNat, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X]
    linear_combination (-1 / 48 : H) * (HahnSeries.single (1 : ℚ) (1 : Qbar) - 1728) ^ 3 * h4
  · simp only [WeierstrassCurve.ofJNe0Or1728, hA, val_inv_sU, map_mul, map_pow, map_sub,
      map_div₀, map_one, map_ofNat, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X]
    linear_combination (1 / 864 : H) * (HahnSeries.single (1 : ℚ) (1 : Qbar) - 1728) ^ 5 * h6

end B3
end ModularCurve
end
end P2MW.S_ModularCurve_B3_b3_specialisationEquivariance
