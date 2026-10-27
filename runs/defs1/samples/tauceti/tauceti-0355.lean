public section

namespace TauCeti

open IsDedekindDomain

open scoped NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

namespace EulerProductData

/-- The ideal delta function, bundled as the identity for Euler-product convolution. -/
noncomputable def delta : EulerProductData K where
  toIdealArithmeticFunction := IdealArithmeticFunction.delta
  isMultiplicative := IdealArithmeticFunction.isMultiplicative_delta

end EulerProductData
end TauCeti
end
