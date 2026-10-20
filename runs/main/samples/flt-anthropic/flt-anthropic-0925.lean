namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace F2AlphaEdge

section Coord

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem coord_tmul_stdBasisVec (i j : Fin 2) (b : B) :
    coord B i (b ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K j) = if i = j then b else 0 := by
  rw [coord_tmul, coordEquiv_stdBasisVec]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

end Coord
end F2AlphaEdge
end
end P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartERing_isPullback_of_act_stdEdge
