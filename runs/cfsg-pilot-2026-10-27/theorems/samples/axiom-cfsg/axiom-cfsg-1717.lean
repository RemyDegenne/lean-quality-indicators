public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H CFSG.Quasithin.E3 Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)

include hc

theorem rk_fsuV (h2 : n = 2) : rk ↥(fsuV T I) = 8 := by
  unfold rk
  rw [hc.card_fsuV h2, show (256 : ℕ) = 2 ^ 8 by norm_num, padicValNat.prime_pow]

end IsCoord
end Setup
end CFSG.Quasithin.H13.Ch9
end
