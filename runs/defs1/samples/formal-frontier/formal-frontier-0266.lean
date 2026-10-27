@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace SpectralStoneDuality.FiniteCoordinates

variable {X : Type u} [TopologicalSpace X]

/-- For a spectral space, finite-stage evaluations form a limiting cone. -/
noncomputable def evaluationConeIsLimit (X : Type u) [TopologicalSpace X]
    [SpectralSpace X] : IsLimit (evaluationCone X) := by
  have hLift : (familyConeIsLimit X).lift (evaluationCone X) =
      familyLift (evaluationCone X) := by
    apply (familyConeIsLimit X).hom_ext
    intro F
    rw [(familyConeIsLimit X).fac]
    exact (familyLift_fac (evaluationCone X) F).symm
  have hHomeo : familyLift (evaluationCone X) =
      (TopCat.isoOfHomeo (spaceHomeomorph X)).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    exact familyLift_evaluation_eq_spaceHomeomorph (X := X) x
  haveI : IsIso ((familyConeIsLimit X).lift (evaluationCone X)) := by
    rw [hLift, hHomeo]
    exact (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of (Family X))
      (spaceHomeomorph X)).isIso_hom
  exact (familyConeIsLimit X).ofPointIso

end SpectralStoneDuality.FiniteCoordinates
end
