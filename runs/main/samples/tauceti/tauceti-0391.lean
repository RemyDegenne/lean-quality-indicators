public noncomputable section

open Complex UpperHalfPlane

open scoped Real

namespace TauCeti

namespace ModularForm

section SegmentDerivRewrites

@[simp]
lemma deriv_fdBoundarySegment4 (H t : ℝ) :
    deriv (fdBoundarySegment4 H) t = -1 / 2 + H * Complex.I - (ρ : ℂ) :=
  (hasDerivAt_fdBoundarySegment4 H t).deriv

end SegmentDerivRewrites
end ModularForm
end TauCeti
end
