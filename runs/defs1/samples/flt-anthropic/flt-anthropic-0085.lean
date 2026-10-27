namespace P2MW.S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

noncomputable section

namespace EDB

namespace Coord

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

variable {B}

abbrev N1' (η : B) : Submodule B (latticeBaseChange 𝒪 K B (stdFullLattice (𝒪 := 𝒪) K)) :=
  Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 0 + η ⊗ₜ[𝒪] stdBasisVec (𝒪 := 𝒪) K 1}

end Coord
end EDB
end
end P2MW.S_CerednikDrinfeld_le_preimage_of_toOmega_mem_chartUnitLocus_of_cerednikDrinfeld_quotient
