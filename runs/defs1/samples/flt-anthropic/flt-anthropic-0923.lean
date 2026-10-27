namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_preimage_opensRange_zeta_eq_of_forall_zeta_comp_eq

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace T4bPreimage

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

def swapO (𝒪 : Type) [CommRing 𝒪] : GL (Fin 2) 𝒪 :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

end T4bPreimage
end
end P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueLevel_preimage_opensRange_zeta_eq_of_forall_zeta_comp_eq
