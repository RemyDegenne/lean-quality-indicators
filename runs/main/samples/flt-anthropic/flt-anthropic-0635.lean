set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

namespace Pic0

@[simp]
theorem coe_pullbackDegZeroHom [FundamentalIdentity K F F']
    (D : Divisor.degZero (K := K) (F := F)) :
    (pullbackDegZeroHom F' D : Divisor K F') = Divisor.pullback F' (D : Divisor K F) := rfl

end Pic0
end AlgebraicCurve
end
end
end
end
