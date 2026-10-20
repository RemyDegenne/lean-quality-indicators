public section

open Finset List Finsupp

namespace Nat

variable {a b m n p : ℕ}

theorem factorization_eq_zero_iff_remainder {p r : ℕ} (i : ℕ) (pp : p.Prime) (hr0 : r ≠ 0) :
    ¬p ∣ r ↔ (p * i + r).factorization p = 0 := by
  refine ⟨factorization_eq_zero_of_remainder i, fun h => ?_⟩
  rw [factorization_eq_zero_iff] at h
  contrapose! h
  refine ⟨pp, ?_, ?_⟩
  · rwa [← Nat.dvd_add_iff_right (dvd_mul_right p i)]
  · contrapose hr0
    exact (add_eq_zero.1 hr0).2

end Nat
end
