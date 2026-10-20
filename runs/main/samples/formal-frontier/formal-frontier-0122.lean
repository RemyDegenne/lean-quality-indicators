public section

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ : Type*} [CommRing R]

variable (I : Ideal R) (n : ℕ)

theorem coeff_restrictedFinFirstCoeff (i : ℕ)
    (f : adicallyRestrictedSubring (σ := Fin (n + 1)) I)
    (β : Fin n →₀ ℕ) :
    coeff β (restrictedFinFirstCoeff I n i f : MvPowerSeries (Fin n) R) =
      coeff (β.cons i) (f : MvPowerSeries (Fin (n + 1)) R) := by
  have h := coeff_coeff_finSuccEquiv (R := R) (n := n)
    (p := (f : MvPowerSeries (Fin (n + 1)) R)) (k := i) (x := β)
  change coeff β (restrictedFirstCoeff I i (restrictedFinSuccEquiv I n f) :
    MvPowerSeries (Fin n) R) = _
  rw [coeff_restrictedFirstCoeff]
  rw [restrictedFinSuccEquiv_coe]
  simpa only [MvPowerSeries.finSuccEquiv, AlgEquiv.trans_apply,
    coeff_coeff_optionEquivLeft] using h

end MvPowerSeries
end
