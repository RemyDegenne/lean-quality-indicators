public section

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ : Type*} [CommRing R]

variable (I : Ideal R) (n : ℕ)

/-- Extract a restricted coefficient series in the first `Fin (n+1)` variable. -/
noncomputable def restrictedFinFirstCoeff (i : ℕ) :
    adicallyRestrictedSubring (σ := Fin (n + 1)) I →+
      adicallyRestrictedSubring (σ := Fin n) I :=
  (restrictedFirstCoeff I i).comp (restrictedFinSuccEquiv I n).toAddMonoidHom

end MvPowerSeries
end
