public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_normalizer_oTwoRes {Y : Subgroup G} {g : G} (hg : ∀ y, y ∈ Y ↔ g * y * g⁻¹ ∈ Y) :
    g ∈ normalizer (oTwoRes Y : Set G) := by
  have hg' : ∀ y, y ∈ Y ↔ g⁻¹ * y * (g⁻¹)⁻¹ ∈ Y := by
    intro y
    have h := hg (g⁻¹ * y * g)
    have h' : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [h'] at h
    simpa using h.symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => sec11_conj_mem_oTwoRes hg x hx, fun hx => ?_⟩
  have h := sec11_conj_mem_oTwoRes (g := g⁻¹) hg' (g * x * g⁻¹) hx
  have h' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
  rwa [h'] at h

end CFSG.OddStandard.SmallF3.Omega
end
