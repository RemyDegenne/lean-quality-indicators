@[expose] public section

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology ContDiff

attribute [local instance 101] secondCountableTopologyEither_of_left

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

variable {f}

/-- The formal multilinear series whose `n`-th term is
`(w₁, ..., wₙ) ↦ (-2πI)^n * L v w₁ * ... * L v wₙ • f v`, as a continuous multilinear map in
the space `W [×n]→L[ℝ] E`.

This is designed so that the Fourier transform of `v ↦ fourierPowSMulRight L f v n` is the
`n`-th derivative of the Fourier transform of `f`.
-/
def fourierPowSMulRight (f : V → E) (v : V) : FormalMultilinearSeries ℝ W E := fun n ↦
  (- (2 * π * I)) ^ n • ((ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (f v)).compContinuousLinearMap
  (fun _ ↦ L v))

end VectorFourier
end
end
