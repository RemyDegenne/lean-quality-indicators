public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

theorem epi_δ_dimensionShiftUp_zero :
    Epi (δ (X := ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
        (coindBotUnit_comp_dimensionShiftUpπ A))
      (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact A) 0 1 rfl) :=
  epi_δ_of_isZero _ 0 (isZero_coindBot_succ A.V 0)

end TauCeti.groupCohomology
end
