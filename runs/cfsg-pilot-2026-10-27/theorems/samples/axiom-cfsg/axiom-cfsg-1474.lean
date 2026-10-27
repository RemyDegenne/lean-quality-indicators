public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F112W

section Weight

variable {G : Type*} [Group G] {H U : Subgroup G}

theorem eq_zero_of_isChiefSeriesFrom_bot {n : ℕ} (h : IsChiefSeriesFrom H U ⊥ n) : n = 0 := by
  cases h with
  | bot => rfl
  | central hstep => exact absurd hstep.2.2.1 not_lt_bot
  | noncentral hstep => exact absurd hstep.2.2.1 not_lt_bot

end Weight
end F112W
end CFSG.Quasithin
end
