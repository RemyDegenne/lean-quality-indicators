public section

namespace Submodule

open Height TauCeti Set Module

variable {ι K : Type*} [LinearOrder ι] [Finite ι] [Field K] [AdmissibleAbsValues K]
  (U : Submodule K (ι → K))

@[simp]
theorem relativeSubspaceHeight_bot : relativeSubspaceHeight (⊥ : Submodule K (ι → K)) = 1 := by
  have h := relativeSubspaceHeight_span_range (linearIndependent_empty_type (ι := Fin 0)
    (R := K) (v := fun _ ↦ (0 : ι → K)))
  rw [range_eq_empty, span_empty] at h
  rw [h, funext (plucker_of_isEmpty _), ← Pi.one_def, mulHeight_one]

end Submodule
end
