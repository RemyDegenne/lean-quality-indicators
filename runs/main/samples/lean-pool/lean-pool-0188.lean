@[expose] public section

open Filter Asymptotics

variable (R : RamanujanTau)

lemma gcd_reduction_pos_a_div (a b : ℕ) (ha : 0 < a) :
    0 < a / Nat.gcd a b :=
  Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) (Nat.gcd_pos_of_pos_left b ha)

end
