namespace P2MW.S_LocalGL2_iwasawa_decomposition_diag

set_option autoImplicit false

open Matrix

namespace LocalGL2

p2m_open

variable {R : Type*} [CommRing R]

variable {K : Type*} [Field K] [Algebra R K]

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem exists_ratio_or_ratio (x y : K) :
    (∃ r : R, x = algebraMap R K r * y) ∨ (∃ r : R, y = algebraMap R K r * x) := by
  obtain ⟨p, s, hs, hx⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨q, t, ht, hy⟩ := IsFractionRing.div_surjective (A := R) y
  have hs0 : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have ht0 : algebraMap R K t ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht

  rcases dvd_total_dvr (p * t) (q * s) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    refine Or.inr ⟨c, ?_⟩
    rw [← hx, ← hy, ← mul_div_assoc, div_eq_div_iff ht0 hs0, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg (algebraMap R K) (by linear_combination hc)
  ·
    refine Or.inl ⟨c, ?_⟩
    rw [← hx, ← hy, ← mul_div_assoc, div_eq_div_iff hs0 ht0, ← map_mul, ← map_mul, ← map_mul]
    exact congrArg (algebraMap R K) (by linear_combination hc)

end LocalGL2
end P2MW.S_LocalGL2_iwasawa_decomposition_diag
