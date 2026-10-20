namespace P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one

attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace HopfAlgebra

namespace RaynaudConservative

p2m_open

open Coalgebra Bialgebra WithConv

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Devissage

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

variable {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]

variable {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']

variable (φ : H →ₐc[R] H') (I' : Ideal H')

def comapIdeal : Ideal H := I'.comap (φ : H →ₐ[R] H')

end Devissage
end RaynaudConservative
end HopfAlgebra
end P2MW.S_HopfAlgebra_bijective_of_bijective_baseChange_of_pow_eq_one
