public noncomputable section

open ContinuousMap

namespace AbstractMeasure

variable {X : Type*} [TopologicalSpace X]

section TopologicalRing

variable {K O : Type*} [NormedField K] [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  (j : O →+* K) (μ : D(X, O))

variable [CompactSpace X]

variable [IsUltrametricDist K]

variable [T2Space X] [TotallyDisconnectedSpace X] [CompleteSpace K]

variable (hj : ∀ a, ‖j a‖ ≤ 1)

@[simp]
theorem extendCoefficients_smul (a : O) :
    extendCoefficients j hj (a • μ) = j a • extendCoefficients j hj μ :=
  finiteProjection_ext _ _ fun q ↦ by
    ext b
    simp

end TopologicalRing
end AbstractMeasure
end
