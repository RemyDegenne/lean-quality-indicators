namespace P2MW.S_CerednikDrinfeld_FormalOmega_range_sup_range_comp_eq_top_of_isPullback_chartVRing

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace F2AlphaE

section Tau

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]

omit [Fact r.Prime] [IsDomain 𝒪] in
theorem algebraMap_pow_eq_zero (π : 𝒪) (n : ℕ) : algebraMap 𝒪 (Avn 𝒪 r π n) π ^ (n + 1) = 0 := by
  rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 (chartVRing 𝒪 r) (Avn 𝒪 r π n), Ideal.Quotient.algebraMap_eq, map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

end Tau
end F2AlphaE
end
end P2MW.S_CerednikDrinfeld_FormalOmega_range_sup_range_comp_eq_top_of_isPullback_chartVRing
