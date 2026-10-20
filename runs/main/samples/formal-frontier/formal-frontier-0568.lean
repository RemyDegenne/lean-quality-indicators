public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

theorem adicallyRestrictedSubring_mono {I J : Ideal R} (hIJ : I ≤ J) :
    adicallyRestrictedSubring (σ := σ) I ≤ adicallyRestrictedSubring J := by
  intro f hf
  exact (mem_adicallyRestrictedSubring J f).mpr
    (((mem_adicallyRestrictedSubring I f).mp hf).mono hIJ)

end MvPowerSeries
end
