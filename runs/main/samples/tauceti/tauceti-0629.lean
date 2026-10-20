public section

namespace PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

theorem continuous_quotientSpanToZModPow (n : ℕ) {q : ℤ_[p]} (hq : (p : ℤ_[p]) ^ n ∣ q) :
    Continuous (quotientSpanToZModPow n hq) :=
  Ideal.Quotient.continuous_lift _ (continuous_toZModPow n) _

end PadicInt
end
