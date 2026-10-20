universe u v

public noncomputable section

open scoped DirectSum

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M]
  [LinearOrder M] [IsOrderedCancelAddMonoid M]

variable (ν : MaxAddDegree R M)

/-- The largest nonzero grade of an associated-graded element. -/
def associatedGradedValue (x : ν.AssociatedGraded) : WithBot M :=
  DirectSum.leadingGrade ν.Component x

end MaxAddDegree
end
