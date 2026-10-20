public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y Z : Type*}

noncomputable section

@[simp]
lemma coeff_pointDifference_left (x y : X) :
    coeff (pointDifference x y) x = 1 - coeff (ofPoint y) x := by
  simp [pointDifference]

end
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
