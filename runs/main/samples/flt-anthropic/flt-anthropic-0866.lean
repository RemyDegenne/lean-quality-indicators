namespace P2MW.S_Deformation_DieudonneModule_map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer

attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl

set_option autoImplicit false

open Function

open scoped TensorProduct

universe u v w

namespace P2FontaineExactM

section Unipotent

open WithConv

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Bialgebra k B] [Coalgebra.IsCocomm k B]

theorem mem_maximalIdeal_of_apply_one_eq_zero
    (hloc : IsLocalRing (CartierDual k B)) (φ : CartierDual k B) (hφ : φ 1 = 0) :
    φ ∈ IsLocalRing.maximalIdeal (CartierDual k B) := by
  haveI := hloc
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨ψ', hψ'⟩ := hu.exists_right_inv
  have h1 := congrArg (fun χ : CartierDual k B => χ 1) hψ'
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply, CartierDual.one_apply, Bialgebra.counit_one,
    CartierDual.toDual_apply, hφ, zero_mul] at h1
  exact zero_ne_one h1

end Unipotent
end P2FontaineExactM
end P2MW.S_Deformation_DieudonneModule_map_baseChange_surjective_injective_fontaineHodge_of_range_eq_hopfKer
