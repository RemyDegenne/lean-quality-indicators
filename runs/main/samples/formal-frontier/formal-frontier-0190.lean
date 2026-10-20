public section

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ γ : Type*} [CommRing R]

@[simp]
theorem restrictedRenameEquiv_coe (I : Ideal R) (e : σ ≃ υ)
    (f : adicallyRestrictedSubring (σ := σ) I) :
    (restrictedRenameEquiv I e f : MvPowerSeries υ R) =
      renameEquiv R e (f : MvPowerSeries σ R) := by
  simp [restrictedRenameEquiv]

end MvPowerSeries
end
