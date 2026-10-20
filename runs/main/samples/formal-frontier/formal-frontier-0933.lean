public section

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ : Type*} [CommRing R]

variable (I : Ideal R) (n : ℕ)

theorem restrictedFinFirstRegroup_injective :
    Function.Injective (restrictedFinFirstRegroup I n) := by
  intro f g h
  apply (restrictedFinSuccEquiv I n).injective
  apply restrictedFirstRegroup_injective I
  change restrictedFirstRegroup I (restrictedFinSuccEquiv I n f) =
    restrictedFirstRegroup I (restrictedFinSuccEquiv I n g) at h
  exact h

end MvPowerSeries
end
