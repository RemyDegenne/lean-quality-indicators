namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_eq_four_mul_add_two_mul_vdet_of_centralizer_apply_eq_zpow_smul_of_isSpecial

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule

namespace DHPhi

variable {r : ℕ} [hr : Fact r.Prime]

section emb

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
  (e𝒪 : ℤ_[r] ≃+* 𝒪) (eK : ℚ_[r] ≃+* K₀) (hcompat : ∀ x : ℤ_[r], algebraMap 𝒪 K₀ (e𝒪 x) = eK (x : ℚ_[r]))

variable {C : Type} [Ring C] (E₀ : C →+* Matrix (Fin 2) (Fin 2) K₀)

def Etr : C →+* Matrix (Fin 2) (Fin 2) ℚ_[r] := (eK.symm.mapMatrix).toRingHom.comp E₀

end emb
end DHPhi
end
end P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasKernelOfDegree_eq_four_mul_add_two_mul_vdet_of_centralizer_apply_eq_zpow_smul_of_isSpecial
