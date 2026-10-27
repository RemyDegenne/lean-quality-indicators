public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace FullCenterTorus

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

open scoped Matrix Pointwise

section Torus

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  {φ : L ≃* antiSp K}

theorem axisTorus_mod (i : Axis) {j : G} (hj : j ∈ pull φ (axisTorus K i)) {z : G}
    (hz : z ∈ pull φ (antiUnipotentCenter K)) :
    z⁻¹ * (j⁻¹ * z * j) ∈ pull φ (rootU K i.swap) := by
  obtain ⟨b, c, rfl⟩ := exists_zc hz
  cases i
  · obtain ⟨δ, ⟨r, hr, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
    rw [conj_zc hr (inv_ne_zero hr) hδ, zc_inv, zc_mul]
    exact zc_mem_U_two.mpr (by rw [mul_inv_cancel₀ hr, one_mul, CharTwo.add_self_eq_zero])
  · obtain ⟨δ, ⟨s, hs, hδ⟩, rfl⟩ := exists_eq_symm_of_mem_pull hj
    rw [conj_zc one_ne_zero hs hδ, zc_inv, zc_mul]
    exact zc_mem_U_one.mpr (by rw [one_pow, one_mul, CharTwo.add_self_eq_zero])

end Torus
end FullCenterTorus
end CFSG.LocalAnalysis.SymplecticFourStandard
end
