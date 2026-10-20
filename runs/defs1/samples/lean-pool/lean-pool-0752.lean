@[expose] public section

open Function Filter Set Metric

open scoped Topology NNReal Uniformity

namespace ExponentialJuliaSetMisiurewicz

noncomputable section

/-- A complex number lies on the embedded real axis. -/
def OnRealAxis (z : ℂ) : Prop := z.im = 0

end
end ExponentialJuliaSetMisiurewicz
end
