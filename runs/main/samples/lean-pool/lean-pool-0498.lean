@[expose] public section

open Filter Polynomial Finset

namespace Zeta32.Arith.Local

lemma VG_of_not_dvd_den {p : ℕ} {r : ℚ} (h : ¬ p ∣ r.den) : VG p r 0 := by
  right
  have : (0 : ℤ) ≤ padicValRat p r := by
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd h]
    simp
  exact_mod_cast this

end Zeta32.Arith.Local
end
