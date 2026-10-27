public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

/-- The canonical local power series of bundled Euler-product data at a height-one prime. -/
noncomputable def localPowerSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  D.toIdealArithmeticFunction.localPowerSeries P

end EulerProductData
end TauCeti
end
