namespace P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite NeronModelInfra

universe u

noncomputable section

namespace P2mStrataGlue

section Step

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

variable {Y : ℕ → Set X} (hY : ∀ i, IsClosed (Y i)) (hYs : ∀ m, ∀ y ∈ Y m, f y = IsLocalRing.closedPoint R)

variable {n : ℕ} (𝔓 : Prev f Y hY n) (𝔇 : Dil f (Y n))

scoped instance : IsIso (𝔇.p ∣_ XK f) := 𝔇.isIso_restrict _ fun _ hx => hx

scoped instance : IsOpenImmersion (iE hY hYs 𝔇) := by
  delta iE; infer_instance

scoped instance : IsOpenImmersion (iQ hY 𝔓 𝔇) := by
  delta iQ; infer_instance

scoped instance : IsOpenImmersion (jE hY hYs 𝔓 𝔇) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.left))

scoped instance : IsOpenImmersion (jQ hY hYs 𝔓 𝔇) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span (iE hY hYs 𝔇) (iQ hY 𝔓 𝔇)) WalkingSpan.right))

scoped instance isSeparated_v : IsSeparated (v hY hYs 𝔓 𝔇) := by
  haveI : ∀ i, IsSeparated ((cov hY hYs 𝔓 𝔇).f i ≫ v hY hYs 𝔓 𝔇) := by
    rintro (_ | _ | _)
    · rw [cov_f_zero, Category.assoc, jE_v]; infer_instance
    · rw [cov_f_left, jE_v]; infer_instance
    · rw [cov_f_right, jQ_v]; infer_instance
  refine isSeparated_of_openCover (v hY hYs 𝔓 𝔇) (cov hY hYs 𝔓 𝔇) ?_
  intro z₁ z₂ h
  by_cases h₁ : v hY hYs 𝔓 𝔇 z₁ ∈ Y n
  · refine ⟨WalkingSpan.left, ?_, ?_⟩ <;> rw [cov_f_left]
    · exact mem_range_jE hY hYs 𝔓 𝔇 z₁ h₁
    · exact mem_range_jE hY hYs 𝔓 𝔇 z₂ (h ▸ h₁)
  · refine ⟨WalkingSpan.right, ?_, ?_⟩ <;> rw [cov_f_right]
    · exact mem_range_jQ hY hYs 𝔓 𝔇 z₁ h₁
    · exact mem_range_jQ hY hYs 𝔓 𝔇 z₂ (h ▸ h₁)

scoped instance locallyOfFiniteType_v : LocallyOfFiniteType (v hY hYs 𝔓 𝔇) := by
  refine IsZariskiLocalAtSource.of_openCover (cov hY hYs 𝔓 𝔇) ?_
  rintro (_ | _ | _)
  · rw [cov_f_zero, Category.assoc, jE_v]; infer_instance
  · rw [cov_f_left, jE_v]; infer_instance
  · rw [cov_f_right, jQ_v]; infer_instance

scoped instance quasiCompact_v [LocallyOfFiniteType f] : QuasiCompact (v hY hYs 𝔓 𝔇) := by
  haveI : IsLocallyNoetherian 𝔇.D := LocallyOfFiniteType.isLocallyNoetherian (𝔇.p ≫ f)
  haveI : QuasiCompact ((E hY 𝔇).ι ≫ 𝔇.p) := inferInstance
  constructor
  intro U hUo hUc
  have hset : v hY hYs 𝔓 𝔇 ⁻¹' U =
      jE hY hYs 𝔓 𝔇 '' (((E hY 𝔇).ι ≫ 𝔇.p) ⁻¹' U) ∪ jQ hY hYs 𝔓 𝔇 '' (𝔓.w ⁻¹' U) := by
    ext z
    constructor
    · intro hz
      rcases cover hY hYs 𝔓 𝔇 z with ⟨e, rfl⟩ | ⟨q, rfl⟩
      · left; refine ⟨e, ?_, rfl⟩
        rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, jE_v] at hz; exact hz
      · right; refine ⟨q, ?_, rfl⟩
        rw [Set.mem_preimage, ← v_jQ_apply hY hYs 𝔓 𝔇 q]; exact hz
    · rintro (⟨e, he, rfl⟩ | ⟨q, hq, rfl⟩)
      · show (jE hY hYs 𝔓 𝔇 ≫ v hY hYs 𝔓 𝔇) e ∈ U
        rw [jE_v]; exact he
      · show v hY hYs 𝔓 𝔇 (jQ hY hYs 𝔓 𝔇 q) ∈ U
        rw [v_jQ_apply]; exact hq
  rw [hset]
  exact ((QuasiCompact.isCompact_preimage (f := (E hY 𝔇).ι ≫ 𝔇.p) U hUo hUc).image
    (jE hY hYs 𝔓 𝔇).continuous).union
    ((QuasiCompact.isCompact_preimage (f := 𝔓.w) U hUo hUc).image (jQ hY hYs 𝔓 𝔇).continuous)

theorem isIso_restrict_XK : IsIso (v hY hYs 𝔓 𝔇 ∣_ XK f) :=
  isIso_morphismRestrict_of_comp (v hY hYs 𝔓 𝔇) (jQ hY hYs 𝔓 𝔇) 𝔓.w (jQ_v hY hYs 𝔓 𝔇) (XK f) 𝔓.isoK
    fun z hz => mem_range_jQ hY hYs 𝔓 𝔇 z fun h => hz (hYs n _ h)

end Step
end P2mStrataGlue
end
end P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
