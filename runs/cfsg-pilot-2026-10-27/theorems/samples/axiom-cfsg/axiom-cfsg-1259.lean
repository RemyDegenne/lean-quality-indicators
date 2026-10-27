public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

open scoped Pointwise commutatorElement

section Y11C

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m11_cent_V_R (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ⊓ centralizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgV, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgc' : ∀ x ∈ l41R t x₁ x₂ rho, g * x = x * g := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hgc x hx).symm
    rcases m11_cent_V_cases h le_rfl (fun x hx => m11_rho_conj_R h.toL41GPh8 hx)
      (m11_R_ne_bot h.toL41GPh8) hgV hgc' with hR | ⟨-, ht⟩
    · exact hR
    · exfalso
      have hRB : l41R t x₁ x₂ rho ≤ baseGrp x₁ x₂ := by
        intro r hr
        rw [← h.rfacts.cent_t]
        exact Subgroup.mem_inf.mpr ⟨hr, mem_invCent_iff.mpr (ht r hr).symm⟩
      have := Subgroup.card_le_of_le hRB
      rw [h.rfacts.card_R, m13_card_B h.toCtx0] at this
      norm_num at this
  · intro r hr
    refine Subgroup.mem_inf.mpr ⟨m11_R_le_V h.toL41GPh8 hr, Subgroup.mem_centralizer_iff.mpr
      fun x hx => ?_⟩
    exact m13_comm_R h hx hr

end Y11C
end CFSG.OddStandard.SmallF3.HarrisU33.S4A
end
