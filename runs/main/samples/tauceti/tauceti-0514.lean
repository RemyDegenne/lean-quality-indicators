public noncomputable section

open Function Set

open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y]

@[simp]
theorem coeff_divisorPullback (f : FiniteHolomorphicMap X Y) (D : WeilDivisor Y) (x : X) :
    WeilDivisor.coeff (divisorPullback f D) x =
      (localMultiplicity f x : ℤ) * WeilDivisor.coeff D (f x) :=
  (rfl)

end TauCeti.RiemannSurface
end
