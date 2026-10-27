namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

noncomputable section

namespace F2AlphaE

section ForcedLine

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

def unitK (K : Type) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (π : 𝒪) (hπ0 : π ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap 𝒪 K π) (fun h => hπ0 ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h))

end ForcedLine
end F2AlphaE
end
end P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algEquiv_chartVRing_isPullback_of_act_stdFullLattice_eq
