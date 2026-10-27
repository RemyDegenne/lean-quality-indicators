public section

namespace CFSG.QuasithinUnique.Setup.X7b

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearCover CFSG.SectionRank.EvenCover

variable {Q : Type} [Group Q]

theorem statedScalars_subgroupOf_eq_bot_of_card_two {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hunit : Subsingleton Kˣ := by
    have h1 : Fintype.card Kˣ = 1 := by
      rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
    exact Fintype.card_le_one_iff_subsingleton.mp h1.le
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  rw [Subsingleton.elim c 1, map_one] at hc
  rw [Subgroup.mem_bot]
  exact Subtype.ext hc.symm

end CFSG.QuasithinUnique.Setup.X7b
end
