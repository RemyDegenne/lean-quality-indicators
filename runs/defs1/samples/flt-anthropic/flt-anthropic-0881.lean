namespace P2MW.S_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm

attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

set_option Elab.async false

open scoped TensorProduct

noncomputable section

namespace HopfAlgebra

namespace OrdBC

p2m_open

section Distrib

variable (R k : Type*) [CommRing R] [CommRing k] [Algebra R k]
  (M E : Type*) [CommRing M] [CommRing E] [Bialgebra R M] [Bialgebra R E]

def inclM : M →ₐc[R] M ⊗[R] E :=
  (Bialgebra.TensorProduct.map (BialgHom.id R M) (Bialgebra.unitBialgHom R E)).comp
    (Bialgebra.TensorProduct.rid R R M).symm.toBialgHom

end Distrib
end OrdBC
end HopfAlgebra
end
end P2MW.S_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
