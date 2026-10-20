public section

open Filter Topology

open scoped BigOperators WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

variable (P : Place k F) {t : F} (hP : P.degree = 1) (ht : P.ord t = 1)

theorem sub_sum_coeff_completionIntegersEquivPowerSeries_symm_mem_filtration
    (f : PowerSeries k) (n : ℕ) :
    ((P.completionIntegersEquivPowerSeries hP ht).symm f : P.Completion) -
      ∑ i : Fin n, algebraMap k P.Completion (PowerSeries.coeff i f) *
        P.completionEmbedding t ^ (i : ℕ) ∈ P.completionPlace.filtration n := by
  have h := P.completionPlace.sub_sum_coeff_powerSeriesExpansion_mem_filtration
    (by simpa using hP) (by simpa using ht :
      P.completionPlace.ord (P.completionEmbedding t) = 1) n
    ((P.completionIntegersEquivPowerSeries hP ht).symm f)
  rw [← P.completionIntegersEquivPowerSeries_apply hP ht,
    AlgEquiv.apply_symm_apply] at h
  exact h

end TauCeti.Place
end
