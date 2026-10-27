public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ComponentClassification.RankTwoStandard

open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

theorem SzMinCounter.false_of_gms5
    {L T R R₂ : Subgroup G} {a : ℕ} {y d : G} (hNS : GMS5NotSylow) (hSw : GMS5Swap)
    (hM : SzMinCounter G L a) (hS : Sec3.SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hall : ∀ g ∈ normalizer (R : Set G), rightConjugate (gmsV L T) g = gmsV L T
  · exact hNS G L T R R₂ a y d hM hS hR₂ hne (hS.isSylowOf_normalizer.of_le le_normalizer
      fun g hg => (rightConjugate_eq_self_iff _ _).mp (hall g hg))
  · push Not at hall
    obtain ⟨g, hg, hgV⟩ := hall
    obtain ⟨E, hE, -, hE4⟩ := hS.sec3.exists_four_le
    have h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) :=
      hE4 ▸ Subgroup.card_le_of_le hE
    obtain ⟨hq, hcomm, hsq, hgR⟩ := hS.swap_of_ne h34 hR₂ h4 hne hg hgV
    exact hSw G L T R R₂ a y d hM hS hR₂ hq hcomm hsq g hg hgR

end CFSG.ComponentClassification.GMS78
end
