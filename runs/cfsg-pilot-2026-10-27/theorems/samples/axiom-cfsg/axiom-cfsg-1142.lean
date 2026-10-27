public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

theorem false_of_odd_dvd_two_pow {d n : ℕ} (hd : Odd d) (hd1 : 1 < d) (h : d ∣ 2 ^ n) : False := by
  have hcop : Nat.Coprime d (2 ^ n) := Nat.Coprime.pow_right n (Nat.coprime_two_right.2 hd)
  have := Nat.Coprime.eq_one_of_dvd hcop h
  omega

end E2
end CFSG.Quasithin
end
