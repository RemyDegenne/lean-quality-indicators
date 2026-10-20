namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom

set_option autoImplicit false

universe u

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve

open MvPolynomial HomogeneousLocalization HomogeneousIdealQuotientGrading

namespace WeierstrassProjModel

p2m_open

namespace ProjBaseChange

attribute [local instance] MvPolynomial.gradedAlgebra

section TwoChartCover

variable {R : Type u} [CommRing R]

def zCofactor (V : WeierstrassCurve.Projective R) : MvPolynomial (Fin 3) R :=
  X 1 ^ 2 + C V.a₁ * X 0 * X 1 + C V.a₃ * X 1 * X 2
    - C V.a₂ * X 0 ^ 2 - C V.a₄ * X 0 * X 2 - C V.a₆ * X 2 ^ 2

end TwoChartCover
end ProjBaseChange
end WeierstrassProjModel
end
end P2MW.S_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
