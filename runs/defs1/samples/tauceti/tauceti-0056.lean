public noncomputable section

open scoped BigOperators

open Function Module NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- The relative affine Euclidean height of a finite tuple, obtained by adjoining the coordinate
one. -/
def arakelovMulHeightAff {ι : Type*} [Finite ι] (x : ι → K) : ℝ :=
  arakelovMulHeight fun o : Option ι ↦ o.elim 1 x

end TauCeti
end
