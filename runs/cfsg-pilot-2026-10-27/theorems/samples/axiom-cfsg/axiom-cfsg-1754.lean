public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal

open scoped MatrixGroups

section Algebra

variable {K : Type*} [Field K]

section Reflections

theorem det_ne_zero_of_invertible {v : Matrix (Fin 2) (Fin 2) K} (h : Invertible (detQ v)) :
    v.det ≠ 0 := by
  have := (isUnit_of_invertible (detQ v)).ne_zero
  rwa [detQ_apply] at this

end Reflections
end Algebra
end CFSG.ClassicalInvolution.Models.OrthogonalPairs
end
