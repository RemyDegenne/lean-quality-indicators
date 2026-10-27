public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem isGomiChevTwo_of_surjective {G X : Type} [Group G] [Group X] [Finite X] [Nontrivial X]
    (hq : CFSG.IsQuasisimple G) (hZ : Odd (Nat.card (center G)))
    (hC : IsChevTwo (G ⧸ center G)) (φ : G →* X) (hφ : Function.Surjective φ) :
    IsGomiChevTwo X := by
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  obtain ⟨g, hg⟩ := hφ x
  have hφ1 : ∃ g, φ g ≠ 1 := ⟨g, by rw [hg]; exact hx⟩
  have hker := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq hφ1
  have hqX := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hφ hφ1
  have hZX := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hq hφ hker
  have hoddX : Odd (Nat.card (center X)) := by
    rw [hZX]
    exact hZ.of_dvd_nat (Subgroup.card_map_dvd (center G) φ)
  have e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hφ hker
  exact IsGomiChevTwo.of_isQuasisimple hqX hoddX
    (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv e hC)

end CFSG.GroupTheory.GomiLeviExc
end
