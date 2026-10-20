public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem contDiff_hamiltonianVectorField (ω : SymplecticForm V) {H : V → ℝ}
    {n : WithTop ℕ∞} (hH : ContDiff ℝ (n + 1) H) :
    ContDiff ℝ n (ω.hamiltonianVectorField H) :=
  ω.toBilinForm.toContinuousBilinearMap.inverse.contDiff.comp
    (hH.fderiv_right le_rfl)

end TauCeti.SymplecticForm
end
