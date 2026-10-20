namespace P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual

attribute [-instance] CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange instIsScalarTowerTensorProduct_definitions

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace HopfTransfer

variable {R : Type*} [CommRing R]

variable {Q : Type*} [CommRing Q] [Algebra R Q]

variable {D : Type*} [CommRing D] [HopfAlgebra R D]

variable (e : Q ≃ₐ[R] D)

theorem comulAlgHom_eq_sum (q : Q) {ιrepr : Type*} (repr : Coalgebra.Repr R (e q) ιrepr) :
    comulAlgHom e q = ∑ i ∈ repr.index, e.symm (repr.left i) ⊗ₜ[R] e.symm (repr.right i) := by
  rw [comulAlgHom_apply', ← repr.eq, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom]

end HopfTransfer
end P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual
