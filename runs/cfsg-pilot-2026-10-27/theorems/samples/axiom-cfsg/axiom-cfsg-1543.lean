public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem DalphaStar_cimg (hN : IsNormalSet D) (g : G) (α : Set G) :
    DalphaStar D (cimg g α) = cimg g (DalphaStar D α) := by
  ext x
  rw [mem_DalphaStar_iff, mem_cimg, mem_DalphaStar_iff]
  constructor
  · rintro ⟨β, hβ, hxβ⟩
    have hmem : β ∈ (fun γ => cimg g γ) '' Dalpha D α := by
      rwa [Dalpha_conj_image hN g]
    obtain ⟨β', hβ', rfl⟩ := hmem
    exact ⟨β', hβ', mem_cimg.mp hxβ⟩
  · rintro ⟨β, hβ, hx⟩
    have hmem : cimg g β ∈ Dalpha D (cimg g α) := by
      rw [← Dalpha_conj_image hN g]
      exact ⟨β, hβ, rfl⟩
    exact ⟨cimg g β, hmem, mem_cimg.mpr hx⟩

end CFSG.OddTranspositions.PartFour
end
