public section

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace UnitaryIdealWeight

/-- The ideal arithmetic function underlying a unitary weight: the restriction of the
underlying multiplicative weight to the nonzero ideals. -/
def toIdealArithmeticFunction (χ : UnitaryIdealWeight K) : IdealArithmeticFunction K :=
  χ.1.toIdealArithmeticFunction

end UnitaryIdealWeight
end TauCeti
end
