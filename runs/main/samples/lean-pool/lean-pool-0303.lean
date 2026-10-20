@[expose] public section

open Polynomial

namespace QuadraticIterates

section

variable (a : ℤ)

lemma finrank_eq_of_nonempty_mulEquiv {n : ℕ}
    (hiso : Nonempty (GaloisGroup a n ≃* WreathPower n)) :
    Module.finrank ℚ ↥(splittingField a n) = 2 ^ (2 ^ n - 1) := by
  rw [← card_galoisGroup_eq_finrank a n, Nat.card_congr hiso.some.toEquiv, card_wreathPower]

end
end QuadraticIterates
end
