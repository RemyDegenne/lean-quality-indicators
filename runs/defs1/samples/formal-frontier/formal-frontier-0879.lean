public section

noncomputable section

open QuadraticAlgebra

namespace QuadraticAlgebra

/-- The quotient of `ℤ[√-5]` by its distinguished norm-two ideal is
`ZMod 2`. -/
@[expose]
def quotientSqrtNegFiveIdealTwoEquiv :
    SqrtNegFiveOrder ⧸ sqrtNegFiveIdealTwo ≃+* ZMod 2 :=
  RingHom.quotientKerEquivOfSurjective sqrtNegFiveModTwo_surjective

end QuadraticAlgebra
end
end
