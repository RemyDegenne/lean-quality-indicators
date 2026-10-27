set_option warningAsError true

@[expose] public section

open CategoryTheory HomogeneousIdeal

open AlgebraicGeometry

namespace ProjectiveSpace

universe u uA uB uσ uτ

section UniversePolymorphic

variable {A : Type uA} {B : Type uB} {σ : Type uσ} {τ : Type uτ}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]

variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Inverse degree-preserving ring maps induce a homeomorphism of
projective-spectrum points, without a common-universe requirement. -/
noncomputable def projectiveSpectrumHomeomorphOfInverseGradedRingHom
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜) :
    ProjectiveSpectrum ℬ ≃ₜ ProjectiveSpectrum 𝒜 where
  toEquiv := projectiveSpectrumEquivOfInverseGradedRingHom f g hfg hgf
  continuous_toFun :=
    (ProjectiveSpectrum.comap f
      (irrelevant_le_map_of_comp_eq_id f g hfg)).continuous
  continuous_invFun :=
    (ProjectiveSpectrum.comap g
      (irrelevant_le_map_of_comp_eq_id g f hgf)).continuous

end UniversePolymorphic
end ProjectiveSpace
end
