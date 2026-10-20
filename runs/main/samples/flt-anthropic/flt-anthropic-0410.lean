namespace P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_eq_three

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace GenRed

theorem exists_eq_C_mul_of_map_residue_eq_zero
    {A : Type} [CommRing A] [IsLocalRing A] (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (x : PowerSeries A) (hx : x.map (IsLocalRing.residue A) = 0) :
    ∃ x' : PowerSeries A, x = PowerSeries.C ϖ * x' := by
  classical
  have hc : ∀ n, ∃ c, PowerSeries.coeff n x = ϖ * c := by
    intro n
    have h0 : IsLocalRing.residue A (PowerSeries.coeff n x) = 0 := by
      have := congrArg (PowerSeries.coeff n) hx
      rwa [PowerSeries.coeff_map, map_zero] at this
    have hm : PowerSeries.coeff n x ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.residue_eq_zero_iff _).mp h0
    rw [hϖ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hcc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hcc]

end GenRed
end P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_eq_three
