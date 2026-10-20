namespace P2MW.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit

set_option autoImplicit false

namespace PowerSeries p2m_export "PowerSeries" "coe_mul algebraMap_apply coeff_mk mk trunc eq_X_mul_shift_add_const map_surjective eval₂_X coeff_coe eval₂_trunc_eq_sum_range eval₂ trunc_trunc_mul_trunc map_X constantCoeff coeff_C_mul coe_one eval₂_C coeff_mul coe_X coeff_map divXPowOrder order isUnit_iff_constantCoeff ext map_C map C X_pow_order_mul_divXPowOrder constantCoeff_divXPowOrder_eq_zero_iff coeff X X_ne_zero coe_C quotient_span_X_sub_C_pow_of_irreducible" end PowerSeries

p2m_open_scoped "PowerSeries" in

namespace Submodule p2m_export "Submodule" "Quotient.eq mem_sup_right smul_mem' mk smul_mem mem_bot mem_span_singleton_self Quotient.mk span smul_induction_on mem_map_of_mem add_mem_sup span_le mem_comap mem_span_insert mem_span_range_iff_exists_fun pow_mem_pow mul_le mem_top mem_span_singleton fg_iff_exists_fin_generating_family mul_mem_mul smul_mem_smul mem_iInf generators nontrivial_iff map_mono map_smul' zero one map_span Quotient.mk_surjective map rec Quotient.nontrivial_iff mem_sup smul_mono_left subset_span module smul_def FG ext factor_mk factorPow map_sup fg_span mem_span_pair mem_sup_left map_le_iff_le_comap restrictScalars_mem" end Submodule

p2m_open_scoped "Submodule" in

p2m_open_scoped "PowerSeries" in

p2m_open_scoped "PowerSeries" in

p2m_open_scoped "PowerSeries" in

p2m_open_scoped "PowerSeries" in

p2m_open_scoped "PowerSeries" in

namespace IsIntegrallyClosed p2m_export "IsIntegrallyClosed" "isIntegral_iff of_equiv" end IsIntegrallyClosed

p2m_open_scoped "IsIntegrallyClosed" in

namespace COMP

open IsLocalRing Polynomial

noncomputable section

set_option synthInstance.maxHeartbeats 800000

section Maps

variable {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [Algebra O R]
  (ϖ : O) [Fact (Irreducible ϖ)]
  (hϖm : algebraMap O R ϖ ∈ maximalIdeal R)

variable (g h w : R) (hw : IsUnit w) (hgm : g ∈ maximalIdeal R) (hhm : h ∈ maximalIdeal R)

abbrev sR : Rh R := algebraMap R (Rh R) (g + h * ↑(hw.unit⁻¹))

end Maps
end
end COMP
end IsIntegrallyClosed
end Submodule
end PowerSeries
end P2MW.S_IsLocalRing_isIntegrallyClosed_of_maximalIdeal_eq_span_of_mul_eq_pow_mul_isUnit
