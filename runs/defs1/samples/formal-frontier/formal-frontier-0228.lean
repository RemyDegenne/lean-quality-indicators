@[expose] public section

open Multiplicative WithZero

noncomputable section

namespace PrimeMultiplicity

variable {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R]

variable {p : R}

/-- The integer-valued multiplicative valuation associated to a prime element
in a domain with well-founded divisibility. -/
noncomputable def valuation (hp : Prime p) : Valuation R ℤᵐ⁰ where
  toFun := valuationDef p
  map_zero' := valuationDef_zero p
  map_one' := valuationDef_one hp
  map_mul' := valuationDef_mul hp
  map_add_le_max' := valuationDef_add_le_max hp

end PrimeMultiplicity
end
end
