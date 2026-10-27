namespace P2MW.S_MvPowerSeries_isNoetherianRing_fin

set_option autoImplicit false

namespace W2MV

open MvPowerSeries

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

section SumRingEquiv

variable (α β : Type*) {R : Type*} [CommSemiring R]

def sumToFun (f : MvPowerSeries (α ⊕ β) R) : MvPowerSeries α (MvPowerSeries β R) :=
  fun a => fun b => f (a.sumElim b)

end SumRingEquiv
end MvPowerSeries
end
end W2MV
end P2MW.S_MvPowerSeries_isNoetherianRing_fin
