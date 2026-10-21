namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

open PiExponentSeshadri.Geometry

open PiExponent.SectionZeroIdeal

variable {X : Scheme.{0}}

theorem power_nonvanishing_sections_of_divisor_lifts
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ)
    (hlift : Function.Surjective
      (fun t : GlobalSections X (L.pow n).sheaf =>
        pullbackSection (zeroIdeal L s).subschemeι t))
    (hgenerate : ∀ y : (zeroIdeal L s).subscheme, ∃ σ :
      GlobalSections (zeroIdeal L s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow n).sheaf),
      y ∈ sectionOpen (zeroIdeal L s).subscheme σ) :
    ∀ x : X, ∃ t : GlobalSections X (L.pow n).sheaf, x ∈ sectionOpen X t := by
  intro x
  by_cases hx : x ∈ sectionOpen X s
  · exact ⟨powerSection s n, sectionOpen_le_powerSection s n hx⟩
  · have hxI : x ∈ (zeroIdeal L s).support := by
      change x ∈ ((zeroIdeal L s).support : Set X)
      rw [zeroIdeal_support]
      exact hx
    have hr : x ∈ Set.range (zeroIdeal L s).subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    obtain ⟨y,rfl⟩ := hr
    obtain ⟨σ,hσ⟩ := hgenerate y
    obtain ⟨t,ht⟩ := hlift σ
    change pullbackSection (zeroIdeal L s).subschemeι t = σ at ht
    refine ⟨t,?_⟩
    have he := pullback_isoOpen_eq (L.pow n) t (zeroIdeal L s).subschemeι
    rw [ht] at he
    change y ∈ (zeroIdeal L s).subschemeι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen t
    exact he.le hσ

end
end PiExponent.NumericalAmpleness
end OAI
