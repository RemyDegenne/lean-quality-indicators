namespace P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic

namespace FinFlatHopf p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom" end FinFlatHopf

p2m_open_scoped "FinFlatHopf" in

set_option autoImplicit false

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf

namespace W4

p2m_open

open TensorProduct WithConv Coalgebra

section generic

variable {R S H L : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing H] [HopfAlgebra R H]
  [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]

def reprOneTmul (h : H) {ι : Type*} (ρ : Coalgebra.Repr R h ι) : Coalgebra.Repr S ((1 : S) ⊗ₜ[R] h) ι where
  index := ρ.index
  left i := (1 : S) ⊗ₜ[R] ρ.left i
  right i := (1 : S) ⊗ₜ[R] ρ.right i
  eq := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← ρ.eq, tmul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraTensorModule.tensorTensorTensorComm_tmul]

end generic
end W4
end FinFlatHopf
end
end FinFlatHopf
end P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic
