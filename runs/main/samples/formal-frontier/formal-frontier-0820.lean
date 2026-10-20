@[expose] public section

open Multiplicative WithZero

noncomputable section

namespace PrimeMultiplicity

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]

variable {p : R}

theorem valuation_ne_zero (hp : Prime p) {r : R} (hr : r ≠ 0) :
    valuation hp r ≠ 0 := by
  rw [valuation_apply_of_ne_zero hp hr]
  exact WithZero.coe_ne_zero

end PrimeMultiplicity
end
end
