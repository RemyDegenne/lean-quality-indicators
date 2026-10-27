public section

namespace TauCeti

namespace QuadraticMap

namespace OrthogonalCompactOpens

open _root_.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) (S : Set Nat.Primes)

variable [FiniteDimensional ℚ V]

/-- The rational special orthogonal diagonal away from `S`. Its integrality comes from the
orthogonal reference family. -/
def awayAdelicSpecialOrthogonalDiagonal :
    specialOrthogonalGroup Q →* RestrictedProductGroupAway S U.specialOrthogonal :=
  (restrictAway S U.specialOrthogonal).comp U.finiteAdelicSpecialOrthogonalDiagonal

end
end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
end
