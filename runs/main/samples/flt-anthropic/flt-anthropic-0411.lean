namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0

set_option autoImplicit false

set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel

open scoped MatrixGroups TensorProduct

namespace PiFibre

theorem exists_formallyUnramified_away_of_isOpenImmersion_fibre
    {R₀ B B' : Type u} [CommRing R₀] [CommRing B] [CommRing B'] [Algebra R₀ B] [Algebra R₀ B']
    (φ : B' →ₐ[R₀] B) (hφ : φ.toRingHom.FiniteType)
    {XM XN : Scheme.{u}} (tM : XM ⟶ Spec (CommRingCat.of R₀)) (tN : XN ⟶ Spec (CommRingCat.of R₀))
    (π : XM ⟶ XN)
    (ι : Spec (CommRingCat.of B) ⟶ XM) [IsOpenImmersion ι] (ι' : Spec (CommRingCat.of B') ⟶ XN) [IsOpenImmersion ι']
    (hι : ι ≫ tM = Spec.map (CommRingCat.ofHom (algebraMap R₀ B)))
    (hι' : ι' ≫ tN = Spec.map (CommRingCat.ofHom (algebraMap R₀ B')))
    (hchart : ι ≫ π = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι')
    {κ : Type u} [Field κ] (τ : R₀ →+* κ)
    (πκ : pullback tM (Spec.map (CommRingCat.ofHom τ)) ⟶ pullback tN (Spec.map (CommRingCat.ofHom τ)))
    (hπκ₁ : πκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ π) (hπκ₂ : πκ ≫ pullback.snd _ _ = pullback.snd _ _)
    (x : ↥(pullback tM (Spec.map (CommRingCat.ofHom τ))))
    (hx : (pullback.fst tM (Spec.map (CommRingCat.ofHom τ))).base x ∈ Set.range ι.base)
    (V₀ : (pullback tM (Spec.map (CommRingCat.ofHom τ))).Opens) (hxV : x ∈ V₀)
    (hV : IsOpenImmersion (V₀.ι ≫ πκ)) :
    ∃ (W : Scheme.{u}) (w : W ⟶ XM), IsOpenImmersion w ∧
      (pullback.fst tM (Spec.map (CommRingCat.ofHom τ))).base x ∈ Set.range w.base ∧
      FormallyUnramified (w ≫ π) := by
  classical
  letI : Algebra R₀ κ := τ.toAlgebra
  let sκ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R₀) := Spec.map (CommRingCat.ofHom τ)

  have eB₁ : Spec.map (CommRingCat.ofHom (algebraMap R₀ B)) ≫ 𝟙 _ = ι ≫ tM := by rw [Category.comp_id, hι]
  have eB'₁ : Spec.map (CommRingCat.ofHom (algebraMap R₀ B')) ≫ 𝟙 _ = ι' ≫ tN := by rw [Category.comp_id, hι']
  have eB₂ : sκ ≫ 𝟙 _ = 𝟙 _ ≫ sκ := by rw [Category.comp_id, Category.id_comp]
  let jB : Spec (CommRingCat.of (B ⊗[R₀] κ)) ⟶ pullback tM sκ :=
    (pullbackSpecIso R₀ B κ).inv ≫ pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) eB₁ eB₂
  let jB' : Spec (CommRingCat.of (B' ⊗[R₀] κ)) ⟶ pullback tN sκ :=
    (pullbackSpecIso R₀ B' κ).inv ≫ pullback.map _ _ _ _ ι' (𝟙 _) (𝟙 _) eB'₁ eB₂
  haveI : IsOpenImmersion jB := inferInstance
  haveI : IsOpenImmersion jB' := inferInstance
  have jB_fst : jB ≫ pullback.fst tM sκ =
      Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R₀] κ))) ≫ ι := by
    simp only [jB, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, pullbackSpecIso_inv_fst']
  have jB_snd : jB ≫ pullback.snd tM sκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B) (B := κ)).toRingHom) := by
    simp only [jB, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact pullbackSpecIso_inv_snd R₀ B κ
  have jB'_fst : jB' ≫ pullback.fst tN sκ =
      Spec.map (CommRingCat.ofHom (algebraMap B' (B' ⊗[R₀] κ))) ≫ ι' := by
    simp only [jB', Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, pullbackSpecIso_inv_fst']
  have jB'_snd : jB' ≫ pullback.snd tN sκ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B') (B := κ)).toRingHom) := by
    simp only [jB', Category.assoc, pullback.lift_snd, Category.comp_id]
    exact pullbackSpecIso_inv_snd R₀ B' κ

  have hxr : x ∈ Set.range jB.base := by
    have hm : x ∈ Set.range (pullback.map _ _ _ _ ι (𝟙 _) (𝟙 _) eB₁ eB₂).base := by
      rw [Scheme.Pullback.range_map]
      exact ⟨hx, ⟨(pullback.snd tM sκ).base x, by simp⟩⟩
    obtain ⟨y, hy⟩ := hm
    refine ⟨(pullbackSpecIso R₀ B κ).hom.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    simp only [jB, Iso.hom_inv_id_assoc]
    exact hy
  obtain ⟨q, rfl⟩ := hxr

  have hqU : q ∈ jB ⁻¹ᵁ V₀ := hxV
  obtain ⟨_, ⟨g, rfl⟩, hqg, hgU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU (jB ⁻¹ᵁ V₀).isOpen
  let lg := Spec.map (CommRingCat.ofHom (algebraMap (B ⊗[R₀] κ) (Localization.Away g)))
  have hlg_mem : ∀ w, lg.base w ∈ PrimeSpectrum.basicOpen g := fun w => by
    have hw : PrimeSpectrum.comap (algebraMap (B ⊗[R₀] κ) (Localization.Away g)) w ∈
        Set.range (PrimeSpectrum.comap (algebraMap (B ⊗[R₀] κ) (Localization.Away g))) := ⟨w, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at hw
    exact hw
  have hsub : Set.range (lg ≫ jB).base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show jB.base (lg.base w) ∈ V₀
    exact hgU (hlg_mem w)
  let l := IsOpenImmersion.lift V₀.ι (lg ≫ jB) hsub
  have hl : l ≫ V₀.ι = lg ≫ jB := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion l := by
    have : IsOpenImmersion (l ≫ V₀.ι) := by rw [hl]; infer_instance
    exact IsOpenImmersion.of_comp l V₀.ι
  have hcmpOI : IsOpenImmersion (lg ≫ jB ≫ πκ) := by
    have : lg ≫ jB ≫ πκ = l ≫ (V₀.ι ≫ πκ) := by rw [← Category.assoc, ← hl, Category.assoc]
    rw [this]
    infer_instance

  let φκ : B' ⊗[R₀] κ →ₐ[R₀] B ⊗[R₀] κ := Algebra.TensorProduct.map φ (AlgHom.id R₀ κ)
  let ψ : B' ⊗[R₀] κ →+* Localization.Away g := (algebraMap (B ⊗[R₀] κ) (Localization.Away g)).comp φκ.toRingHom
  have hcmp : lg ≫ jB ≫ πκ = Spec.map (CommRingCat.ofHom ψ) ≫ jB' := by
    apply pullback.hom_ext
    · have h1 : (lg ≫ jB ≫ πκ) ≫ pullback.fst tN sκ =
          lg ≫ Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[R₀] κ))) ≫
            Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι' := by
        rw [Category.assoc, Category.assoc, hπκ₁, ← Category.assoc jB, jB_fst, Category.assoc, hchart]
      have h2 : (Spec.map (CommRingCat.ofHom ψ) ≫ jB') ≫ pullback.fst tN sκ =
          Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B' (B' ⊗[R₀] κ))) ≫ ι' := by
        rw [Category.assoc, jB'_fst]
      rw [h1, h2, ← Category.assoc, ← Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom ψ))]
      congr 1
      simp only [lg, ← Spec.map_comp]
      congr 1
      all_goals
        ext b
        change algebraMap (B ⊗[R₀] κ) (Localization.Away g) (algebraMap B (B ⊗[R₀] κ) (φ b)) =
          algebraMap (B ⊗[R₀] κ) (Localization.Away g) (φκ (algebraMap B' (B' ⊗[R₀] κ) b))
        simp [φκ, Algebra.TensorProduct.algebraMap_apply]
    · have h1 : (lg ≫ jB ≫ πκ) ≫ pullback.snd tN sκ =
          lg ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B) (B := κ)).toRingHom) := by
        rw [Category.assoc, Category.assoc, hπκ₂, jB_snd]
      have h2 : (Spec.map (CommRingCat.ofHom ψ) ≫ jB') ≫ pullback.snd tN sκ =
          Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R₀) (A := B') (B := κ)).toRingHom) := by
        rw [Category.assoc, jB'_snd]
      rw [h1, h2]
      simp only [lg, ← Spec.map_comp]
      congr 1
      all_goals
        ext k
        change algebraMap (B ⊗[R₀] κ) (Localization.Away g) ((1 : B) ⊗ₜ k) =
          algebraMap (B ⊗[R₀] κ) (Localization.Away g) (φκ ((1 : B') ⊗ₜ k))
        simp [φκ]
  have hψOI : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ)) := by
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ) ≫ jB') := by rw [← hcmp]; exact hcmpOI
    exact IsOpenImmersion.of_comp _ jB'
  have hψ : ψ.FormallyUnramified := by
    have : FormallyUnramified (Spec.map (CommRingCat.ofHom ψ)) := inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mp this

  obtain ⟨f, hf, hfU⟩ := exists_formallyUnramified_away_of_baseChange φ hφ q.asIdeal g hqg hψ
  refine ⟨_, Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f))) ≫ ι, inferInstance, ?_, ?_⟩
  swap
  ·
    rw [Category.assoc, hchart, ← Category.assoc, ← Spec.map_comp]
    have h1 : FormallyUnramified (Spec.map (CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom (algebraMap B (Localization.Away f)))) :=
      (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr hfU
    exact MorphismProperty.comp_mem _ _ _ h1 inferInstance

  have hpt : (pullback.fst tM sκ).base (jB.base q) =
      ι.base (PrimeSpectrum.comap (algebraMap B (B ⊗[R₀] κ)) q) := by
    rw [← Scheme.Hom.comp_apply, jB_fst, Scheme.Hom.comp_apply]
    rfl
  have hmemf : PrimeSpectrum.comap (algebraMap B (B ⊗[R₀] κ)) q ∈
      Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hf
  obtain ⟨w, hw⟩ := hmemf
  refine ⟨w, ?_⟩
  rw [hpt, Scheme.Hom.comp_apply, ← hw]
  rfl

end PiFibre
end P2MW.S_ModularCurve_XHDRModelAtP_exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
