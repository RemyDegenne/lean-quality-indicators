public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix

open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)

namespace IsCoord

variable {S} {K : Type} [Field K] [Fintype K] [CharP K 2] {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)

include hc

theorem natCard : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hc.card]

end IsCoord
end Setup
end CFSG.Quasithin.H13.Ch9
end
