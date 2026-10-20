public section

open CategoryTheory Limits

open scoped DirectSum

namespace TauCeti

universe u v

namespace InternalGrading

section OfGradedObject

variable (R : Type u) [Ring R] (X : GradedObject ℤ (ModuleCat.{v} R))

/-- The external direct sum of a graded object carries the internal grading by its canonical
component copies. -/
noncomputable def ofGradedObject : InternalGrading R (⨁ p : ℤ, X p) where
  piece := gradedObjectPiece R X
  isInternal := by
    -- `IsInternal` uses additive recomposition; its linear version has the same underlying map.
    change Function.Bijective (DirectSum.coeLinearMap (gradedObjectPiece R X))
    rw [← gradedObjectPiecesEquiv_symm_eq_coeLinearMap]
    exact (gradedObjectPiecesEquiv R X).symm.bijective

end OfGradedObject
end InternalGrading
end TauCeti
end
