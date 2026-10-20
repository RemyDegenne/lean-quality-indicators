set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain

open scoped Classical

namespace ArtinL.Abelian

section Finite

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

def IsUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ ∈ inertiaGroup K M v, ψ σ = 1

end Finite
end ArtinL.Abelian
end
