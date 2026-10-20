namespace P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq

set_option autoImplicit false

open scoped TensorProduct

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

namespace HopfAlgebra

namespace FC

p2m_open

theorem finrank_eq_natCard_algHom
    (K : Type) [Field K] (Af : Type) [CommRing Af] [Algebra K Af] [Module.Finite K Af]
    (hpts : Nat.card (Af →ₐ[K] AlgebraicClosure K) = Module.finrank K Af) :
    Module.finrank K Af = Nat.card (Af →ₐ[K] AlgebraicClosure K) := hpts.symm

end FC
end HopfAlgebra
end P2MW.S_HopfAlgebra_map_hopfKer_eq_hopfKer_of_comul_mul_tmul_eq
