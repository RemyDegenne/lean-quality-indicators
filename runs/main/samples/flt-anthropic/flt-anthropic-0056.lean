namespace P2MW.S_Padic_index_range_powMonoidHom_units_of_ne_two

open Polynomial

namespace Ws26U4

section RatBasic

open Padic

variable {p : ℕ} [hp : Fact p.Prime]

theorem natCast_prime_ne_zero : ((p : ℚ_[p])) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

end RatBasic
end Ws26U4
end P2MW.S_Padic_index_range_powMonoidHom_units_of_ne_two
