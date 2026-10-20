namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mFlatIsog

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

section StalkDim

variable {K : Type u} [Field K]

theorem ringKrullDim_stalk_eq {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    [IsIntegral X] [IsIntegral Y] (h : X ⟶ Y) [IsFinite h] [Surjective h] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (h.base x)) := by

  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := h.base x) (U := ⊤) trivial
  have hU : IsAffineOpen (h ⁻¹ᵁ V) := hV.preimage h
  have hxU : x ∈ h ⁻¹ᵁ V := hyV
  haveI : Nonempty (h ⁻¹ᵁ V) := ⟨⟨x, hxU⟩⟩
  haveI : Nonempty V := ⟨⟨h.base x, hyV⟩⟩

  set φ : Γ(Y, V) ⟶ Γ(X, h ⁻¹ᵁ V) := h.appLE V (h ⁻¹ᵁ V) le_rfl with hφ
  have hφapp : φ = h.app V := (Scheme.Hom.appLE_eq_app _).symm ▸ rfl
  have hint : φ.hom.IsIntegral := by
    rw [hφapp]
    exact (h.finite_app V hV).to_isIntegral
  have hinj : Function.Injective φ.hom := by
    rw [hφapp]
    rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : h ⁻¹ᵁ Y.basicOpen b = ⊥ := by
      rw [Scheme.preimage_basicOpen, hb, Scheme.basicOpen_zero]
    have h2 : Y.basicOpen b = ⊥ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hy
      obtain ⟨x', rfl⟩ := h.surjective y
      have : x' ∈ (h ⁻¹ᵁ Y.basicOpen b) := hy
      rw [h1] at this
      exact this
    exact (basicOpen_eq_bot_iff b).mp h2

  set px := hU.primeIdealOf ⟨x, hxU⟩ with hpx
  set py := hV.primeIdealOf ⟨h.base x, hyV⟩ with hpy
  have hcomap : px.asIdeal.comap φ.hom = py.asIdeal := by
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE (f := h) V hV (h ⁻¹ᵁ V) hU le_rfl hxU
    rw [← hpx] at h1
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    exact h2

  letI := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : h ⁻¹ᵁ V)
  letI := Y.presheaf.algebra_section_stalk (⟨h.base x, hyV⟩ : V)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) px.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk (h.base x)) py.asIdeal :=
    hV.isLocalization_stalk ⟨h.base x, hyV⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height px.asIdeal (X.presheaf.stalk x),
    IsLocalization.AtPrime.ringKrullDim_eq_height py.asIdeal (Y.presheaf.stalk (h.base x))]

  obtain ⟨algA, hftA⟩ := exists_algebra_finiteType fX (h ⁻¹ᵁ V) hU
  obtain ⟨algB, hftB⟩ := exists_algebra_finiteType fY V hV
  letI := algA
  letI := algB
  have key := height_comap_eq K φ.hom hint hinj px.asIdeal
  rw [hcomap] at key
  rw [key]

end StalkDim
end P2mFlatIsog
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd
