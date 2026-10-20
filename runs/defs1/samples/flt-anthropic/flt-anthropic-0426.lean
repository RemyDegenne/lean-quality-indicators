namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and

attribute [-instance] instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra

set_option autoImplicit false

open IsLocalRing TrivSqZeroExt

namespace DDF2

section Scale

variable {k : Type} [Field k]

noncomputable def scale (c : k) : DualNumber k →+* DualNumber k :=
  (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).toRingHom

end Scale
end DDF2
end P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_maximalIdeal_eq_map_sup_span_singleton_sup_sq_of_isProrepresentedBy_deformations_of_not_and
