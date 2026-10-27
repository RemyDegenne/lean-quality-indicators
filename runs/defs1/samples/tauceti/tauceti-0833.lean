public section

namespace TauCeti

open Matrix

/-- The ordinary-character table of A₅ in the exponent-`30` coefficient ring used by the solver. -/
def alternatingGroupFiveExponentCharacterTable :
    Matrix AlternatingGroupFiveClassIndex AlternatingGroupFiveClassIndex (Cyclotomic 30) :=
  fun i j ↦ Cyclotomic.evalCoeffs (Int.castRingHom (Cyclotomic 30)) (Cyclotomic.zeta 30 ^ 6)
    (alternatingGroupFiveCandidateCharacterTable i j)

end TauCeti
end
