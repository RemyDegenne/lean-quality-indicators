set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace AlgebraicCurve

namespace TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

variable {R F j}

variable (R F j)

def chartInfOpen : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens := (ιInf R F j).opensRange

end TwoChartIntegralModel
end AlgebraicCurve
end
