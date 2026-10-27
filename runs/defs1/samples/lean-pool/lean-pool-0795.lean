@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

open scoped nonZeroDivisors Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance poleDivisorConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance poleDivisorConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The effective negative part of the principal divisor of `x`. -/
def finiteExtensionPoleDivisor (x : L) : FiniteExtensionDivisor K L :=
  by
    classical
    let D := finiteExtensionPrincipalDivisor K L x
    exact -(D.filter (fun v => D v < 0))

end
end BGS.HasseWeil
end
