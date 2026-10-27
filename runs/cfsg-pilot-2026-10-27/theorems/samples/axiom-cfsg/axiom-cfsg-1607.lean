public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint

open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Three

theorem commute_x₄_of_mem_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {b : G}
    (hb : b ∈ yamadaM₃ d t) (hbg : b * ((d.leviThree : L) : G) = ((d.leviThree : L) : G) * b)
    (c : d.Γ) : b * ((d.x₄ c : L) : G) = ((d.x₄ c : L) : G) * b := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have hbT : b ∈ translationsW₂ d t :=
    (h.yamadaL₃_eq_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102) ▸
      (Subgroup.mem_inf.1 hb).1
  have hbE := ((h.mem_centralizerW₂Y₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1
    ((h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hbT).1).2
  have hXW₂ : ((d.x₄ c : L) : G) ∈ yamadaW₂ d t := mem_sup_left ⟨d.x₄ c, d.x₄_mem_W c, rfl⟩
  have hgX : ((d.x₄ c : L) : G) * ((d.leviThree : L) : G) =
      ((d.leviThree : L) : G) * ((d.x₄ c : L) : G) :=
    mem_centralizer_iff.1 (leviLong_map_le_centralizer_U₄ d ⟨_, d.leviThree_mem_leviLong, rfl⟩)
      _ ⟨d.x₄ c, d.x₄_mem_U₄ c, rfl⟩
  have hgb : ((d.leviThree : L) : G) * b * ((d.leviThree : L) : G)⁻¹ = b := by
    rw [← hbg, mul_inv_cancel_right]
  have hgX' : ((d.leviThree : L) : G) * ((d.x₄ c : L) : G) * ((d.leviThree : L) : G)⁻¹ =
      ((d.x₄ c : L) : G) := by
    rw [← hgX, mul_inv_cancel_right]
  have hfix : ((d.leviThree : L) : G) * (b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹) *
      ((d.leviThree : L) : G)⁻¹ = b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ := by
    calc ((d.leviThree : L) : G) * (b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹) *
          ((d.leviThree : L) : G)⁻¹ =
        (((d.leviThree : L) : G) * b * ((d.leviThree : L) : G)⁻¹) *
          (((d.leviThree : L) : G) * ((d.x₄ c : L) : G) * ((d.leviThree : L) : G)⁻¹) *
          (((d.leviThree : L) : G) * b * ((d.leviThree : L) : G)⁻¹)⁻¹ *
          (((d.leviThree : L) : G) * ((d.x₄ c : L) : G) * ((d.leviThree : L) : G)⁻¹)⁻¹ := by
          group
      _ = b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ := by rw [hgb, hgX']
  have h1 := h.eq_one_of_mem_yamadaY₂_of_conj_leviThree d hlay (hbE _ hXW₂) hfix
  calc b * ((d.x₄ c : L) : G) =
      b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ * (((d.x₄ c : L) : G) * b) := by
        group
    _ = ((d.x₄ c : L) : G) * b := by rw [h1, one_mul]

end Three
end Setup
end CFSG.LocalAnalysis.EvenBN.TrialityD4
end
