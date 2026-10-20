public section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

theorem nsmulSeries_succ (n : ℕ) :
    F.nsmulSeries (n + 1) = subst ![F.nsmulSeries n, PowerSeries.X] F.toPowerSeries := by
  rw [nsmulSeries, nsmulSeries, succ_nsmul, add_apply, val_tautologicalPoint]

end FormalGroup
end
