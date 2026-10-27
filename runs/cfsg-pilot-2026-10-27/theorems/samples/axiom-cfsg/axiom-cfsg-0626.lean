public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint

open CFSG.LocalAnalysis.EvenBN.Common

open CFSG.ABGLocalTools (IsSylowOf)

open scoped MatrixGroups

namespace ProductDecompAux

section Phase1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem dg_K3_E1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K : Subgroup G} (hK : IsLayerComponent d t K)
    (hc : ⁅kThree d t K, (kThree d t K)ᵍ[t]⁆ = ⊥) :
    dg (kThree d t K) t hc (eOne d t K) = d.Y.map L.subtype := by
  have ht2 : t * t = 1 := h.t_mul_t
  obtain ⟨-, -, ⟨hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩⟩ := A2_sylow h d hp hK
  obtain ⟨⟨hK3E, hK3O, hK3Q, hK3Z, hN3, hK3i, hK3c, hN3Q⟩, -, -⟩ := A3_structure h d hp hK
  have hT4Y := (T4_series_free h d hp).2.1
  have hle : dg (kThree d t K) t hc (eOne d t K) ≤ d.Y.map L.subtype := by
    intro y hy
    obtain ⟨e, heK3, heE, rfl⟩ := mem_dg_iff.1 hy
    rw [← hT4Y]
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [hE1]
      exact mul_mem (mem_sup_left heE) (mem_sup_right (conj_mem_map_conj_inv t heE))
    · exact range_diagonalHom_le hc ht2 ⟨⟨e, heK3⟩, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_dg hK3i hK3E, hE4, card_Y_map d]

end Phase1
end ProductDecompAux
end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
end
