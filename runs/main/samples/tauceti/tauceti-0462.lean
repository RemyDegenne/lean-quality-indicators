public section

namespace MvPolynomial

open scoped ENNReal NNReal

variable {σ R : Type*}

section Semiring

variable [CommSemiring R]

theorem le_weightedIndex_sum {ι : Type*} (r : σ → ℕ) (a : σ → R) {s : Finset ι}
    {P : ι → MvPolynomial σ R} {t : ℝ≥0∞} (h : ∀ i ∈ s, t ≤ weightedIndex r a (P i)) :
    t ≤ weightedIndex r a (∑ i ∈ s, P i) := by
  rw [le_weightedIndex_iff]
  intro d hd
  rw [map_sum, map_sum]
  exact Finset.sum_eq_zero fun i hi ↦ (le_weightedIndex_iff r a (P i) t).mp (h i hi) d hd

end Semiring
end MvPolynomial
end
