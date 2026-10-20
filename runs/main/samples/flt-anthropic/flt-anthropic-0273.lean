namespace P2MW.S_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel

set_option autoImplicit false

namespace E143TI

open AlgebraicCurve ModularCurve

universe u

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map φ) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

end E143TI
end P2MW.S_ModularCurve_FullLevel_sub_inMax_of_mem_inertiaSubgroupIn_of_inStalk_twoChartIntegralModel
