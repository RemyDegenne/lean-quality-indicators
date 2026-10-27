public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

open CFSG.Blueprint (LieModel)

open CFSG.Assembly.LowTwoRank (StatedLieTag)

open scoped Pointwise

section TwoComponents

variable {G : Type} [Group G] [Finite G]

theorem uc22p20p_excl_false_two (hG : Global22f) (hB : ListBNonabelian) (D : Data G)
    (h20_1 : S20_1_124 D) (h1930 : H1930 D) {L : Subgroup G} (hL : L ∈ calL D.T D.M)
    {A₁ A₂ : Subgroup (Bar2 L)} (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hsup : A₁ ⊔ A₂ = ⊤)
    {X : Type} [Group X] [Finite X] (e₁ : X ≃* ↥A₁) (hq : CFSG.Open.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) {t : StatedLieTag} {m n : ℕ}
    (hex : uc22p20oExcl t m n ∨ (t = .PSU ∧ m = 5 ∧ n = 2 ∧ Subgroup.center X ≠ ⊥))
    (hM : LieModel (X ⧸ Subgroup.center X) t m 2 n) : False := by
  obtain ⟨p, hp, hp2, h⟩ := hG.excl X hq hodd t m n hex hM
  rcases h with ⟨rfl, hX⟩ | ⟨hX, hBor⟩
  · obtain ⟨E, -, hE, hEc⟩ := uc22p20p_embed_rankWit e₁ hX
    exact uc22p20o_core D hB h1930 h20_1 hL Nat.prime_three hp2 E hE hEc (Or.inl rfl)
  · obtain ⟨E, -, hE, hEc⟩ := uc22p20p_embed_rankWit e₁ hX
    have hS := uc22p20p_sylowBar_isSylowOf D hL
    obtain ⟨F, hFA, hFN, hF, hFc⟩ := uc22p20p_embed_borelWit e₁
      (uc22p20p_isSylowOf_inf_left hcomm hsup hS) hBor
    exact uc22p20o_core D hB h1930 h20_1 hL hp hp2 E hE hEc
      (Or.inr ⟨F, hF, hFc, fun x hx => uc22p20p_normalizer_of_split hcomm hsup hS (hFA hx) (hFN hx)⟩)

end TwoComponents
end CFSG.LocalAnalysis.UniquenessCase.UC22
end
