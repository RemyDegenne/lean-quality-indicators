public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y Z : Type*}

noncomputable section

/-- A divisor is effective when every coefficient is nonnegative. -/
def IsEffective (D : WeilDivisor X) : Prop :=
  ∀ x, 0 ≤ coeff D x

end
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
