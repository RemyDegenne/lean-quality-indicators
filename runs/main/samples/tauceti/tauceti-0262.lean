public section

open IsLocalRing ValuativeRel

namespace TauCeti.Padic

local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

@[simp]
theorem teichmullerLift_padic_five_two_sq : teichmullerLift ℚ_[5] 2 ^ 2 = -1 := by
  rw [← map_pow, ← teichmullerLift_padic_five_four]
  norm_num

end TauCeti.Padic
end
