@[expose] public section

noncomputable section

open scoped ContDiff

namespace EulerFinitePathTensor

variable {K E V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Coordinates, given by `ContinuousLinearMap.pi (fun w => (ContinuousLinearMap.id ℝ (E
[×n]→L[ℝ] V)).flipMultilinear (fun i => Module.finBasis ℝ E (w i)))`. -/
def coordinates (n : ℕ) :
    (E [×n]→L[ℝ] V) →L[ℝ] ((Fin n → Fin (Module.finrank ℝ E)) → V) :=
  ContinuousLinearMap.pi (fun w =>
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] V)).flipMultilinear
      (fun i => Module.finBasis ℝ E (w i)))

end EulerFinitePathTensor
end
end
