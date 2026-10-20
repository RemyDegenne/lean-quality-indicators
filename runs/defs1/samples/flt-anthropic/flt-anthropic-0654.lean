namespace P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope

set_option maxHeartbeats 800000

set_option autoImplicit false

universe u v w

open IsLocalRing

open scoped TensorProduct

open IsLocalRing

open scoped TensorProduct

open IsLocalRing Polynomial

open Polynomial

open Polynomial

p2m_reactivate

open Polynomial

open scoped TensorProduct

p2m_reactivate

open Polynomial IsLocalRing

p2m_reactivate

namespace P1Arch

open IsLocalRing Polynomial

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

p2m_reactivate

p2m_reactivate

section QuotTensorK

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (K : Type u) [Field K] (W : Type u) [CommRing W] [IsDomain W] [Algebra W K] [IsFractionRing W K] (B : Type u) [CommRing B] [Algebra W B]

noncomputable def quotMaxAlgEquivTensorQuotK
    [Module.Finite K (K ⊗[W] B)]
    (𝔪 : Ideal (K ⊗[W] B)) [𝔪.IsMaximal]
    [Module.Free W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B)))]
    [Module.Finite W (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B)))] :
    ((K ⊗[W] B) ⧸ 𝔪) ≃ₐ[K]
      K ⊗[W] (B ⧸ 𝔪.comap (algebraMap B (K ⊗[W] B))) := by
  set Q : Ideal B := 𝔪.comap (algebraMap B (K ⊗[W] B)) with hQ
  let g : (K ⊗[W] B) →ₐ[K] K ⊗[W] (B ⧸ Q) :=
    Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ W Q)
  have hg : ∀ z ∈ 𝔪, g z = 0 := by
    haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (K ⊗[W] B) :=
      IsLocalization.tensorRight K (nonZeroDivisors W)
    have h𝔪 : 𝔪 = Q.map (algebraMap B (K ⊗[W] B)) :=
      (IsLocalization.map_comap (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (K ⊗[W] B) 𝔪).symm
    intro z hz
    rw [h𝔪] at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, rfl⟩
      change g ((1 : K) ⊗ₜ[W] q) = 0
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem.mpr hq, TensorProduct.tmul_zero]
    · exact map_zero g
    · intro y z _ _ hy hz; rw [map_add, hy, hz, add_zero]
    · intro a y _ hy; rw [smul_eq_mul, map_mul, hy, mul_zero]
  let Φ : ((K ⊗[W] B) ⧸ 𝔪) →ₐ[K] K ⊗[W] (B ⧸ Q) :=
    Ideal.Quotient.liftₐ 𝔪 g hg
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨y, rfl⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id K K)
      (Ideal.Quotient.mkₐ W Q) Function.surjective_id Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  haveI : Module.Finite K ((K ⊗[W] B) ⧸ 𝔪) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K 𝔪).toLinearMap Ideal.Quotient.mk_surjective
  have hdim : Module.finrank K ((K ⊗[W] B) ⧸ 𝔪) =
      Module.finrank K (K ⊗[W] (B ⧸ Q)) := by
    rw [finrank_quotient_tensor_eq_finrank_quotientK K W B 𝔪, Module.finrank_baseChange]
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := Φ.toLinearMap)).mpr hsurj
  exact AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩

end QuotTensorK
end P1Arch
end P2MW.S_IsDiscreteValuationRing_charpoly_mulLeft_quotient_eq_finprod_single_slope
