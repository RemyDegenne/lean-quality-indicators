set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace ModularCurve

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

attribute [local instance] instDecidableEqRatFuncRat

def jLinePlaceZero : Place ℚ ℚ⟮jq⟯ :=
  Place.congrRingEquiv jLineRingEquiv (RingHom.map_rat_algebraMap jLineRingEquiv.toRingHom)
    (placeOfPoint ℚ 0)

end ModularCurve
end
