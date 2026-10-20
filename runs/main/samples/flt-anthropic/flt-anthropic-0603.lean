namespace P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder

set_option autoImplicit false

open scoped MatrixGroups

p2m_open

noncomputable section

namespace CerednikDrinfeld

namespace Omega

namespace GlobalCurrent

p2m_open

section PUTree

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀] {ϖ : R}
  {K : Type} [Field K] [Algebra K₀ K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_algebraMap_pos (hϖ : Irreducible ϖ) : 0 < Valued.v (algebraMap K₀ K (algebraMap R K₀ ϖ)) :=
  lt_of_le_of_ne zero_le' (Ne.symm ((Valuation.ne_zero_iff _).mpr
    ((map_ne_zero _).mpr (algebraMap_ne_zero_of_irreducible hϖ))))

end PUTree
end GlobalCurrent
end Omega
end CerednikDrinfeld
end
end P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder
