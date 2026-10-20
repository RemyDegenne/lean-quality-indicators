public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y Z : Type*}

noncomputable section

/-- The subgroup of divisors of weighted degree zero for a weight function on points.

For a curve over a field `k`, the intended weight is `x ↦ [κ(x) : k]`, giving the formal
degree-zero divisor group before principal divisors are introduced. -/
@[expose] noncomputable def weightedDegreeZeroSubgroup (w : X → ℤ) : AddSubgroup (WeilDivisor X) :=
  (weightedDegree w).ker

end
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
