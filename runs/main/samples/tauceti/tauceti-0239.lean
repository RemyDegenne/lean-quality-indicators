public section

open HahnSeries LaurentSeries

open scoped LaurentSeries

namespace TauCeti.puiseuxField

@[simp]
theorem levelPowerBasis_dim (K : Type*) [Field K] (d : ℕ+) :
    (levelPowerBasis K d).dim = d := by
  rw [levelPowerBasis, PowerBasis.map_dim, LaurentSeries.Level.powerBasis_dim]

end TauCeti.puiseuxField
end
