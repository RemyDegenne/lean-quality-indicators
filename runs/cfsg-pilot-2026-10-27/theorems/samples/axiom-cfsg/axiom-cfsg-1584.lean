public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

open CFSG.Wreathed.CentralSL2Abelianization

open TwoRankLowerBound.Helpers

section Induced

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem twist_clifford {θ : CentralExtension F b m hm heven → ℂ}
    (hθ : θ ∈ BlocksIrr (CentralExtension F b m hm heven))
    {χ : semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ) → ℂ}
    (hχ : χ ∈ BlocksIrr (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
      (twistStabilizer hSigma θ)))
    (hres : ∀ (g : CentralExtension F b m hm heven)
      (hg : (SemidirectProduct.inl g : SemilinearExtension F b m hm heven Sigma hSigma) ∈
        semilinearInertia (twistStabilizer hSigma θ)), χ ⟨SemidirectProduct.inl g, hg⟩ = θ g) :
    (∀ ρ, twistInduced hSigma θ χ ρ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) ∧
      twistInduced hSigma θ χ ρ 1 = ((twistStabilizer hSigma θ).index : ℂ) * θ 1) ∧
    Function.Injective (twistInduced hSigma θ χ) ∧
    (∀ ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma),
      0 < BlocksInnerProduct (fun g => ξ (SemidirectProduct.inl g)) θ ↔
      ∃ ρ, ξ = twistInduced hSigma θ χ ρ) ∧
    (∀ C : Finset Sigma, (∀ q : Sigma ⧸ twistStabilizer hSigma θ,
        ∃! σ, σ ∈ C ∧ (σ : Sigma ⧸ twistStabilizer hSigma θ) = q) →
      (∀ ρ, (fun g => twistInduced hSigma θ χ ρ (SemidirectProduct.inl g)) =
        ∑ σ ∈ C, fieldTwist hSigma σ θ) ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' → fieldTwist hSigma σ θ ≠ fieldTwist hSigma σ' θ) ∧
      (∀ ρ, ∀ σ ∈ C, BlocksInnerProduct (fun g => twistInduced hSigma θ χ ρ
          (SemidirectProduct.inl g)) (fieldTwist hSigma σ θ) = 1)) ∧
    (∀ ρ (g : CentralExtension F b m hm heven) (τ : Sigma), τ ∉ twistStabilizer hSigma θ →
      twistInduced hSigma θ χ ρ ⟨g, τ⟩ = 0) := by
  set N := baseLayer F b m hm heven Sigma hSigma with hN
  set θN := layerFunction (Sigma := Sigma) (hSigma := hSigma) θ with hθNdef
  have hθclass := classFunction_of_blocksIrr hθ
  have hθN : θN ∈ BlocksIrr N := layerFunction_mem_blocksIrr hθ
  have hJ : characterInertiaSubgroup N θN = semilinearInertia (twistStabilizer hSigma θ) := by
    rw [hθNdef, characterInertiaSubgroup_layer hSigma hθclass]
    rfl
  have : IsMulCommutative (InertiaQuotient N θN) := quotient_baseLayer_isMulCommutative _
  obtain ⟨W, i₁, i₂, i₃, τ₂, -, hτ₂⟩ := hχ
  let τ₁ : Representation ℂ (characterInertiaSubgroup N θN) W :=
    τ₂.comp (MulEquiv.subgroupCongr hJ).toMonoidHom
  have hτ₁ : ∀ x : characterInertiaSubgroup N θN, τ₁.character x =
      χ ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma), hJ ▸ x.2⟩ :=
    fun x => congrFun hτ₂ _
  have hρN : ∀ (x : characterInertiaSubgroup N θN)
      (hx : (x : SemilinearExtension F b m hm heven Sigma hSigma) ∈ N),
      τ₁.character x = θN ⟨x, hx⟩ := by
    intro x hx
    rw [hτ₁]
    have hx' := eq_inl_left_of_mem_baseLayer hx
    have h2 : (⟨(x : SemilinearExtension F b m hm heven Sigma hSigma), hJ ▸ x.2⟩ :
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
          (twistStabilizer hSigma θ)) =
        ⟨SemidirectProduct.inl (x : SemilinearExtension F b m hm heven Sigma hSigma).left,
          by rw [hx']; exact hJ ▸ x.2⟩ := Subtype.ext hx'.symm
    rw [h2, hres]
    rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    abelian_inertia_extension_induction_character_family N hθN τ₁ hρN
  let φ : characterInertiaSubgroup N θN →* (twistStabilizer hSigma θ) :=
    (SemidirectProduct.rightHom.comp (characterInertiaSubgroup N θN).subtype).codRestrict
      (twistStabilizer hSigma θ) fun x =>
        (hJ ▸ x.2 : (x : SemilinearExtension F b m hm heven Sigma hSigma) ∈
          semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
            (twistStabilizer hSigma θ))
  have hker : N.subgroupOf (characterInertiaSubgroup N θN) = φ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_baseLayer_iff, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact Subtype.ext hx
    · intro hx
      exact congrArg Subtype.val hx
  have hsurj : Function.Surjective φ := by
    intro σ
    refine ⟨⟨SemidirectProduct.inr (σ : Sigma), ?_⟩, rfl⟩
    rw [hJ, mem_semilinearInertia_iff]
    exact σ.2
  let e : InertiaQuotient N θN ≃* (twistStabilizer hSigma θ) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  have he : ∀ x : characterInertiaSubgroup N θN,
      e (x : InertiaQuotient N θN) = ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right,
        (hJ ▸ x.2 : (x : SemilinearExtension F b m hm heven Sigma hSigma) ∈
          semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma)
            (twistStabilizer hSigma θ))⟩ := fun x => rfl
  have hΘ : ∀ ρ : (twistStabilizer hSigma θ) →* ℂˣ, twistInduced hSigma θ χ ρ =
      inertiaInducedCharacter N τ₁ (ρ.comp e.toMonoidHom) := by
    intro ρ
    rw [inertiaInducedCharacter, twistInduced, ← inducedFunction_congr_subgroup hJ]
    congr 1
    funext x
    rw [quotientTwist, hτ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he]
  have hresIP : ∀ ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ,
      BlocksInnerProduct (fun n : N => ξ n) θN =
        BlocksInnerProduct (fun g => ξ (SemidirectProduct.inl g)) θ := by
    intro ξ
    rw [restrict_baseLayer_eq, hθNdef, blocksInnerProduct_layerFunction]
  have hθ1 : θN 1 = θ 1 := rfl
  have hindex : (characterInertiaSubgroup N θN).index = (twistStabilizer hSigma θ).index := by
    rw [hJ, index_semilinearInertia]
  refine ⟨fun ρ => ?_, fun ρ ρ' h => ?_, fun ξ hξ => ?_, fun C hC => ?_, fun ρ g τ hτ => ?_⟩
  · rw [hΘ]
    obtain ⟨hirr, hdeg⟩ := h1 (ρ.comp e.toMonoidHom)
    refine ⟨hirr, ?_⟩
    rw [hdeg, hindex, hθ1]
  · rw [hΘ, hΘ] at h
    have h' := h2 h
    refine MonoidHom.ext fun s => ?_
    have := DFunLike.congr_fun h' (e.symm s)
    simpa using this
  · rw [← hresIP, h3 ξ hξ]
    constructor
    · rintro ⟨σ', rfl⟩
      refine ⟨σ'.comp e.symm.toMonoidHom, ?_⟩
      rw [hΘ]
      congr 1
      refine MonoidHom.ext fun q => ?_
      simp
    · rintro ⟨ρ, rfl⟩
      exact ⟨ρ.comp e.toMonoidHom, hΘ ρ⟩
  · have hCH : ∀ q : SemilinearExtension F b m hm heven Sigma hSigma ⧸
        characterInertiaSubgroup N θN, ∃! h, h ∈ C.image (SemidirectProduct.inr :
          Sigma →* SemilinearExtension F b m hm heven Sigma hSigma) ∧
          (h : SemilinearExtension F b m hm heven Sigma hSigma ⧸
            characterInertiaSubgroup N θN) = q := by
      rw [hJ]
      exact image_inr_reps hSigma (twistStabilizer hSigma θ) C hC
    obtain ⟨hsum, hdist, -, hmult⟩ := h4 _ hCH
    have hconj : ∀ σ : Sigma, conjugateNormalCharacter N θN (SemidirectProduct.inr σ) =
        layerFunction (fieldTwist hSigma σ θ) := by
      intro σ
      rw [hθNdef, conjugateNormalCharacter_layer hSigma hθclass, SemidirectProduct.right_inr]
    have hinj : Set.InjOn (SemidirectProduct.inr : Sigma →*
        SemilinearExtension F b m hm heven Sigma hSigma) C :=
      fun _ _ _ _ h => SemidirectProduct.inr_injective h
    refine ⟨fun ρ => ?_, fun σ hσ σ' hσ' hne => ?_, fun ρ σ hσ => ?_⟩
    · apply layerFunction_injective (Sigma := Sigma) (hSigma := hSigma)
      rw [layerFunction_sum, ← restrict_baseLayer_eq, hΘ, hsum, Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun σ _ => hconj σ
    · intro heq
      apply hdist (SemidirectProduct.inr σ) (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)
        (SemidirectProduct.inr σ') (Finset.mem_image.mpr ⟨σ', hσ', rfl⟩)
        (fun h => hne (SemidirectProduct.inr_injective h))
      rw [hconj, hconj, heq]
    · have h6 := hmult (ρ.comp e.toMonoidHom) (SemidirectProduct.inr σ)
        (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)
      rw [hconj, ← hΘ, restrict_baseLayer_eq, blocksInnerProduct_layerFunction] at h6
      exact h6
  · rw [hΘ]
    apply h5 (by rw [hJ]; exact semilinearInertia_normal hSigma (twistStabilizer hSigma θ))
    rw [hJ, mem_semilinearInertia_iff]
    exact hτ

end Induced
end CFSG.Wreathed.CentralSL2
end
