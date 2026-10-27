public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint Matrix

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation CFSG.Assembly.LowTwoRank

open scoped commutatorElement

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem x_mem_L_of_psp4 {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (h : Lem711Cfg X L K x y) (θ : ↥L ≃* StatedProj (StatedSp 2 F)) : x ∈ L := by
  have := h.normal
  have := h.soc.simple
  have hnabP : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := h.exists_noncomm
    exact ⟨θ a, θ b, fun h' => hab (θ.injective (by rw [map_mul, map_mul, h']))⟩
  have : IsSimpleGroup (StatedProj (StatedSp 2 F)) := θ.symm.isSimpleGroup
  have hZ := CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnabP
  obtain ⟨ρ, hinj, hρW, -, -⟩ := CFSG.ComponentClassification.OutcomeLocal.socle_extension
    (W := L) h.centralizer_eq_bot θ hZ
  have h1 : ρ x ∈ (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map ρ := ⟨x, h.x_mem_commutator, rfl⟩
  rw [Subgroup.map_commutator] at h1
  have hle : ⁅(⊤ : Subgroup (MulAut (StatedProj (StatedSp 2 F)))),
      (⊤ : Subgroup (MulAut (StatedProj (StatedSp 2 F))))⁆ ≤
      (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact Sp4Out.commutator_mem_inner hodd a b
  obtain ⟨g, hg⟩ := hle (Subgroup.commutator_mono le_top le_top h1)
  have hw : ρ ((θ.symm g : ↥L) : X) = ρ x := by
    rw [hρW, MulEquiv.apply_symm_apply, hg]
  have := hinj hw
  rw [← this]
  exact (θ.symm g).2

end Lem711Cfg
end CFSG.GH74.GLS
end
