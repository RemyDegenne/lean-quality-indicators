public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup CFSG.Open

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

open CFSG.LieType.Ree.ReeTag

open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff isSylowOf_of_card)

open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

open scoped commutatorElement

attribute [instance] Setup.fld Setup.fin Setup.chr

namespace Setup

variable {G : Type} [Group G] [Finite G]
  (h : Setup G)

theorem pull_le_normalizer {M M' : Subgroup (ModGL F4.tag h.K)}
    (hM : M ≤ normalizer (M' : Set (ModGL F4.tag h.K))) :
    h.pull M ≤ normalizer (h.pull M' : Set G) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := h.mem_pull.1 hx
  have hyN := hM hy
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := h.mem_pull.1 hz
    rw [← map_inv, ← map_mul, ← map_mul, emb_mem_pull]
    exact (mem_normalizer_iff.1 hyN w).1 hw
  · intro hz
    obtain ⟨w, hw, hwz⟩ := h.mem_pull.1 hz
    have hz' : z = h.emb (y⁻¹ * w * y) := by
      rw [map_mul, map_mul, map_inv, hwz]
      group
    rw [hz', emb_mem_pull]
    have h1 := (mem_normalizer_iff.1 (inv_mem hyN) w).1 hw
    rwa [inv_inv] at h1

end Setup
end CFSG.LocalAnalysis.EvenBN.TwoF4
end
