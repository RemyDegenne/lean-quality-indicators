public section

open Module

namespace IsGalois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem exists_intermediateField_finrank_pow_prime_ge {p : ℕ} (hp : p.Prime) {n : ℕ}
    (M : IntermediateField K L) (hM : p ^ n ∣ finrank M L) :
    ∃ N ≥ M, finrank N L = p ^ n := by
  grind [exists_intermediateField_finrank_pow_prime_le_le hp (by simp) hM le_top]

end IsGalois
end
