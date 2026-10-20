public section

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X Y : Scheme.{u}}

@[reassoc]
theorem fromOfGlobalSections_naturality (f : A →+* Γ(Y, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) (g : X ⟶ Y) :
    g ≫ fromOfGlobalSections 𝒜 f hf =
      fromOfGlobalSections 𝒜 (g.appTop.hom.comp f)
        (by rw [← Ideal.map_map, hf, Ideal.map_top]) := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f)
    (by rw [← Ideal.map_map, hf, Ideal.map_top])).hom_ext _ _ fun ⟨d, t, hd, ht⟩ ↦ ?_
  have hchart := toBasicOpenOfGlobalSections_naturality 𝒜 f g hd ht
  have hy := fromOfGlobalSections_resLE 𝒜 f hf hd ht
  have hx := fromOfGlobalSections_resLE 𝒜 (g.appTop.hom.comp f)
    (by rw [← Ideal.map_map, hf, Ideal.map_top]) hd ht
  rw [← hy, ← hx] at hchart
  have h := congrArg (fun e ↦ e ≫ (basicOpen 𝒜 t).ι) hchart
  simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, openCoverOfMapIrrelevantEqTop,
    Scheme.openCoverOfIsOpenCover, RingHom.comp_apply] using h

end AlgebraicGeometry.Proj
end
