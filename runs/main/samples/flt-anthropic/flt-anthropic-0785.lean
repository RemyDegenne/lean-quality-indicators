namespace P2MW.S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat

set_option autoImplicit false

namespace StalkBC

p2m_open

section LocalPS

open MvPowerSeries IsLocalRing

variable {K : Type*} [CommRing K]

variable [IsLocalRing K]

theorem resL_eq_zero_of_mem_map_span_pair_sup (g : MvPowerSeries (Fin 2) K) (hg : constantCoeff g ∈ maximalIdeal K)
    (t : MvPowerSeries (Fin 2) K ⧸ Ideal.span {g})
    (ht : t ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) K), X 1} ⊔
      (maximalIdeal K).map (C : K →+* MvPowerSeries (Fin 2) K)).map (Ideal.Quotient.mk (Ideal.span {g}))) :
    resL g hg t = 0 := by
  apply resL_eq_zero_of_mem_map_maximalIdeal g hg t
  refine Ideal.map_mono ?_ ht
  refine sup_le ?_ ?_
  · rw [Ideal.span_le]
    rintro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl <;>
      simp only [SetLike.mem_coe, mem_maximalIdeal_iff_constantCoeff, constantCoeff_X, Ideal.zero_mem]
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal_iff_constantCoeff, constantCoeff_C]
    exact ha

end LocalPS
end StalkBC
end P2MW.S_AdicCompletion_exists_ringEquiv_mvPowerSeries_quotient_map_of_tensorProduct_of_flat
