public section

set_option warningAsError true

namespace MvPowerSeries

variable {R σ υ γ : Type*} [CommRing R]

@[simp]
theorem restrictedRenameEquiv_trans (I : Ideal R) (e : σ ≃ υ) (f : υ ≃ γ) :
    (restrictedRenameEquiv I e).trans (restrictedRenameEquiv I f) =
      restrictedRenameEquiv I (e.trans f) := by
  apply RingEquiv.ext
  intro p
  apply Subtype.ext
  change renameEquiv R f (renameEquiv R e (p : MvPowerSeries σ R)) =
    renameEquiv R (e.trans f) p
  rw [← AlgEquiv.trans_apply, renameEquiv_trans]

end MvPowerSeries
end
