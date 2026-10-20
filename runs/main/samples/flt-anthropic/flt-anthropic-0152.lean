namespace P2MW.S_CerednikDrinfeld_FormalOmega_associated_algEquiv_chartERing_xi_eta_of_isPullback

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace F2AlphaEdge

section Assembly

variable {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]

variable (hdvr : IsDiscreteValuationRing 𝒪) (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)

variable (g₁ : GL (Fin 2) K) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) (n : ℕ)

omit [Fact r.Prime] [IsDomain 𝒪] [IsFractionRing 𝒪 K] in
theorem gact_mul (B : Type) [CommRing B] [Algebra 𝒪 B] (g h : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (g * h)⁻¹ d = DeligneDatum.pullback π B g⁻¹ (DeligneDatum.pullback π B h⁻¹ d) :=
  (Omega.action K π).act_mul B g h d

end Assembly
end F2AlphaEdge
end
end P2MW.S_CerednikDrinfeld_FormalOmega_associated_algEquiv_chartERing_xi_eta_of_isPullback
