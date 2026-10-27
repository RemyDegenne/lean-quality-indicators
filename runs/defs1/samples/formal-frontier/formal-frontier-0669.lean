public section

noncomputable section

open QuadraticAlgebra

namespace QuadraticAlgebra

/-- The distinguished ideal of `ℤ[√-5]` obtained as the kernel of reduction
to `ZMod 2`. -/
@[expose]
def sqrtNegFiveIdealTwo : Ideal SqrtNegFiveOrder :=
  RingHom.ker sqrtNegFiveModTwo

end QuadraticAlgebra
end
end
