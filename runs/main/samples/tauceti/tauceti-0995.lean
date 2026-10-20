public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y Z : Type*}

noncomputable section

@[simp]
lemma coeff_sum_ofPoint [DecidableEq X] (s : Finset X) (x : X) :
    coeff (∑ y ∈ s, ofPoint y) x = if x ∈ s then 1 else 0 := by
  simp [coeff, ofPoint, Finsupp.finsetSum_apply, Finsupp.single_apply]

end
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
