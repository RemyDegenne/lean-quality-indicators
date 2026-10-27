public section

namespace CFSG.LocalAnalysis.EvenBN.G2

section Part11

open Subgroup CFSG.Open

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff mem_centralizerMod_iff commutator_mem_iff_proj)

open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open scoped commutatorElement Pointwise MatrixGroups

open CFSG.ABGLocalTools (IsSylowOf)

open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (mem_sup_iff_of_le_normalizer mem_sup_iff_of_le_normalizer' Sl2Pair mem_normalizer_of_pow_mem
    le_normalizer_of_commutator_mem conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer card_conj pCoreOf_conj mem_normalizer_of_conj_eq
    mem_normalizer_pCoreOf conj_mono mem_conj_iff)

open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf mem_normalizer_sup)

open CFSG.LocalAnalysis.EvenBN.TrialityD4 (card_sup_mul_card_inf_eq_D4)

namespace ProductLiftsAux

namespace Cfg

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {t : G} {U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast : Subgroup G}
  (c : Cfg K t U Y W F M D P N₁ N₂ Λ₁ Λ₂ J₃ J₄ J S Ast)

include c

theorem card_αY_le {A₂ B₁ B₂ : Subgroup G} (hA₂ : A₂ = Λ₂ ⊓ Ast)
    (hB₁ : B₁ = pCoreOf 2 (⁅Λ₁, Λ₁⁆ : Subgroup G))
    (hB₂ : B₂ = pCoreOf 2 (⁅Λ₂, Λ₂⁆ : Subgroup G)) :
    Nat.card ((B₁ ⊔ Y) ⊓ F : Subgroup G) ≤ Nat.card K ^ 2 * Nat.card Y := by
  have hYF : Y ≤ F := c.Y_le_W.trans c.W_le_F
  have hB₁N : B₁ ≤ normalizer (Y : Set G) := (c.B₁_le_P hB₁).trans c.P_norm_Y
  have h1 : (B₁ ⊔ Y) ⊓ F = Y ⊔ (F ⊓ B₁) := by
    rw [inf_comm, dedekind hYF hB₁N, sup_comm]
  have hFB : F ⊓ B₁ ≤ normalizer (Y : Set G) := inf_le_right.trans hB₁N
  have h2 := card_sup_mul_card_inf_eq_D4 hFB
  have h3 : Y ⊓ (F ⊓ B₁) = B₁ ⊓ Y := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxY, hxFB⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨(mem_inf.1 hxFB).2, hxY⟩
    · obtain ⟨hxB, hxY⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨hxY, mem_inf.2 ⟨hYF hxY, hxB⟩⟩
  rw [h3, c.card_B₁_inf_Y hB₁, c.B₁_inf_F_eq hB₁, c.card_α hA₂ hB₁ hB₂, c.card_Y] at h2
  rw [h1, c.B₁_inf_F_eq hB₁]
  have hq : 0 < Nat.card K ^ 3 := pow_pos Nat.card_pos 3
  have h4 : Nat.card (Y ⊔ (B₁ ⊓ M) : Subgroup G) = Nat.card K ^ 2 * Nat.card K ^ 4 :=
    Nat.eq_of_mul_eq_mul_right hq (h2.trans (by ring))
  rw [h4, c.card_Y]

end Cfg
end ProductLiftsAux
end Part11
end CFSG.LocalAnalysis.EvenBN.G2
end
