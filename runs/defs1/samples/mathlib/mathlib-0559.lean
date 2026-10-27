@[expose] public section

namespace PowerSeries

open Filter

open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] (c : ℝ) (f : PowerSeries R)

namespace IsRestricted

variable [IsUltrametricDist R]

/-- Restricted power series as an subring of `PowerSeries R`. -/
def subring (c : ℝ) :  Subring (PowerSeries R) :=
  MvPowerSeries.IsRestricted.subring (fun _ ↦ c)

end IsRestricted
end PowerSeries
end
