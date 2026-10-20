public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

theorem normCoeff_eq_eulerProduct (D : EulerProductData K) :
    normCoeff K D.toIdealArithmeticFunction =
      ArithmeticFunction.eulerProduct D.localArithmeticFactor :=
  IdealArithmeticFunction.normCoeff_eq_eulerProduct D.isMultiplicative

end EulerProductData
end TauCeti
end
