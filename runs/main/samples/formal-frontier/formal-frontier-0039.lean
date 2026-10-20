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

@[simp]
theorem projClosedPointsEquivOfInverseGradedRingHom_apply_coe
    (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ)
    (hgf : g.comp f = GradedRingHom.id 𝒜)
    (p : closedPoints (AlgebraicGeometry.Proj ℬ)) :
    (projClosedPointsEquivOfInverseGradedRingHom f g hfg hgf p).1 =
      ProjectiveSpectrum.comapFun f
        (irrelevant_le_map_of_comp_eq_id f g hfg) p.1 :=
  rfl

end UniversePolymorphic
end ProjectiveSpace
end
