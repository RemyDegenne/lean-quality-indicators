@[expose] public section

namespace LeanPool.PythagoreanPolynomialParametrization

open MvPolynomial

/-- g_16 = c_16·a_16·b_16

In the paper: (xSub+(1-wSub)²xSub)(ySub+(1+wSub)zSub)ySub -/
noncomputable def g16Param : RatPoly 16 := c16Param * a16Param * b16Param

end LeanPool.PythagoreanPolynomialParametrization
end
