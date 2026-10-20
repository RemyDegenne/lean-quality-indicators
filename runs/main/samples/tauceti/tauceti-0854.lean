public noncomputable section

open Complex UpperHalfPlane

open scoped Real

namespace TauCeti

namespace ModularForm

section Segments

lemma hasDerivAt_fdBoundarySegment4 (H t : ℝ) :
    HasDerivAt (fdBoundarySegment4 H) (-1 / 2 + H * Complex.I - (ρ : ℂ)) t := by
  have h := HasDerivAt.scomp_of_eq (x := t)
    (hg := AffineMap.hasDerivAt_lineMap (a := (ρ : ℂ)) (b := -1 / 2 + H * Complex.I))
    (hh := (hasDerivAt_id t).sub_const 3) (hy := rfl)
  simp only [one_smul] at h
  exact h.congr_of_eventuallyEq <| Filter.Eventually.of_forall fun s ↦ by
    rw [fdBoundarySegment4_apply]
    rfl

end Segments
end ModularForm
end TauCeti
end
