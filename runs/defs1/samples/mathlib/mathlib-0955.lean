@[expose] public section

variable {ι : Type*}

namespace GradedMonoid

section Defs

variable (A : ι → Type*)

/-- A graded version of `Mul`. Multiplication combines grades additively, like
`AddMonoidAlgebra`. -/
class GMul [Add ι] where
  /-- The homogeneous multiplication map `mul` -/
  mul {i j} : A i → A j → A (i + j)

end Defs
end GradedMonoid
end
