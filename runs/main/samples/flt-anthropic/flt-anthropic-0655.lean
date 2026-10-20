namespace P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_add_eq_of_smul_eq_zero

set_option autoImplicit false

universe u v w

namespace FontaineTors

open Deformation Deformation.TruncWitt Deformation.DieudonneModule

variable {p : ℕ} [hp : Fact p.Prime]

variable {k : Type u} [CommRing k] {A : Type v} [CommRing A] [Bialgebra k A]

variable {ℛ : Type w} [CommRing ℛ] {π : ℛ →+* A}

namespace Inst

open scoped TensorProduct

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]

variable {k : Type v} [CommRing k] [Algebra 𝓞 k]

variable {ℛ : Type w} [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]

theorem inputs (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    @Inputs p _ k _ (k ⊗[𝓞] ℛ) inferInstance inferInstance ℛ _
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom where
  crit _ _ ha hVa := mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom p hp hk hker ℛ ha hVa
  lift n u hu :=
    @TruncWitt.exists_mem_fontaineKer_truncate_eq_of_frobeniusFun_mem_fontaineKer ℛ _ p _
      (k ⊗[𝓞] ℛ) inferInstance
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom
      (SpecialFibre.reduction_surjective hk) (SpecialFibre.ker_reduction_eq_span hk hker).le n u hu

end Inst
end FontaineTors
end P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_add_eq_of_smul_eq_zero
