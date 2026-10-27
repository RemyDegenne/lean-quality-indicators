public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem false_of_alt_small
    (hCI : GSLit.ClassicalInvolutionInput) (h : Config G p w v L K) {m : ℕ} (hm5 : 5 ≤ m)
    (hm7 : m ≤ 7) (e : ↥K ⧸ Open.fusionZStar ↥K ≃* alternatingGroup (Fin m)) : False := by
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  obtain ⟨-, z, hz2, huniq, -⟩ := LocalAnalysis.small_alternating_even_center_exact_quaternion_cover
    hm5 hm7 h.quasisimple_quot h.even_card_center (eZ.symm.trans e)
  have hrY : CFSG.pRank 2 (↥K ⧸ pPrimeCore 2 ↥K) ≤ 1 :=
    UnbalancedAltSeven.pRank_le_one_of_unique hz2 huniq
  rw [FooteLit.pRank_quotient_pPrimeCore] at hrY
  exact h.false_of_pRank_le_one hCI hrY

end Config
end CFSG.ComponentClassification.HarrisLit.L35
end
