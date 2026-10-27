set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups

open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld

namespace FormalOmega

section AdicPoints

variable {𝒪 : Type} [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)

variable (R : Type) [CommRing R] [Algebra 𝒪 R]

def coordToTensor (n : ℕ) (w : Fin 2 → R) : latticeBaseChange 𝒪 K (modPow π R n) (stdFullLattice K) :=
  ∑ i : Fin 2, (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) (w i)) ⊗ₜ[𝒪] stdBasisVec K i

end AdicPoints
end FormalOmega
end CerednikDrinfeld
end
