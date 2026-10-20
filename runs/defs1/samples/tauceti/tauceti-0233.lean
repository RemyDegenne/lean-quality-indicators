public section

open HahnSeries LaurentSeries

open scoped LaurentSeries

namespace TauCeti.LaurentSeries

variable {K : Type*} [Field K]

namespace Level

/-- The level parameter `u`, whose `d`-th power is the base parameter. -/
noncomputable def parameter (K : Type*) [Field K] (d : ℕ+) : Level K d :=
  (ringEquivLaurentSeries K d).symm (single 1 1)

end Level
end TauCeti.LaurentSeries
end
