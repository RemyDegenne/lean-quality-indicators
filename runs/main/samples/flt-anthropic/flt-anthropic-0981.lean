namespace P2MW.S_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange

set_option autoImplicit false

open TensorProduct DirectSum

universe u

p2m_reactivate

open GradedBaseChange in
theorem solution
    {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]
    (A : Type u) [CommRing A] [Algebra S A] (𝓐 : ℕ → Submodule S A) [GradedAlgebra 𝓐]
    (B : Type u) [CommRing B] [Algebra T B] [Algebra S B] [IsScalarTower S T B]
    (𝓑 : ℕ → Submodule T B) [GradedAlgebra 𝓑]
    (ϑ : A →ₐ[S] B) (hϑdeg : ∀ n, ∀ x ∈ 𝓐 n, ϑ x ∈ 𝓑 n)
    (hbc : ∀ n, IsBaseChange T ((ϑ.toLinearMap.restrict (p := 𝓐 n) (q := (𝓑 n).restrictScalars S) (hϑdeg n))
      : 𝓐 n →ₗ[S] (𝓑 n).restrictScalars S)) :
    Function.Bijective
      (Algebra.TensorProduct.lift ϑ (IsScalarTower.toAlgHom S T B) (fun _ _ => Commute.all _ _) : A ⊗[S] T →ₐ[S] B) := by
  refine ⟨fun x y hxy => ?_, fun b => ⟨ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b, φ_ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc b⟩⟩
  have := congrArg (ψ T A 𝓐 B 𝓑 ϑ hϑdeg hbc) hxy
  rwa [ψ_φ, ψ_φ] at this

end P2MW.S_GradedAlgebra_bijective_tensorProduct_lift_of_forall_isBaseChange
