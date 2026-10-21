namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter

open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter

open scoped BigOperators

open MeasureTheory Set Filter

open scoped BigOperators unitInterval

variable {N : ℕ}

theorem varthetaSmear_pressure (x : Fin N → CubeSpace) :
    Integrable (fun y => varthetaSmear x y^(5/3:ℝ)) ∧
      (∫ y, varthetaSmear x y^(5/3:ℝ)) ≤ radialPressureAverage x := by
  let f (R : CubeRotation) (y : CubeSpace) : ℝ :=
    ∑ i, cubeOverlap (rotatedCubeCloud R x i-WithLp.ofLp (rotationIsometry R⁻¹ y))
  have hn (R : CubeRotation) (y : CubeSpace) : 0 ≤ f R y :=
    Finset.sum_nonneg (fun _ _ => cubeOverlap_nonneg _)
  have hi (R : CubeRotation) : Integrable (fun y => f R y^(5/3:ℝ)) :=
    ((rotatedCloud_coordinates_preserving R).integrable_comp
      (translation_average_pressure (rotatedCubeCloud R x)).1.aestronglyMeasurable).2
        (translation_average_pressure (rotatedCubeCloud R x)).1
  have he (R : CubeRotation) : (∫ y, f R y^(5/3:ℝ)) =
      ∫ y, (∑ i, cubeOverlap (rotatedCubeCloud R x i-y))^(5/3:ℝ) :=
    (rotatedCloud_coordinates_preserving R).integral_comp (rotatedCloud_coordinates_embedding R)
      (fun y => (∑ i, cubeOverlap (rotatedCubeCloud R x i-y))^(5/3:ℝ))
  have hb (R : CubeRotation) : (∫ y, f R y^(5/3:ℝ)) ≤ translatedPressureAverage (rotatedCubeCloud R x) := by
    rw [he]
    exact (translation_average_pressure _).2
  have hp := average_pressure (μ := cubeRotationMeasure) (rotatedCloud_density_measurable x)
    hn (fun R y => cubeOverlap_sum_le _ _)
    hi (fun R => (hb R).trans (translatedPressureAverage_le _))
  have hae (y : CubeSpace) : (∫ R, f R y ∂cubeRotationMeasure) = varthetaSmear x y :=
    (varthetaSmear_translation_rotation x y).symm
  change Integrable (fun y => (∫ R, f R y ∂cubeRotationMeasure)^(5/3:ℝ)) ∧
    (∫ y, (∫ R, f R y ∂cubeRotationMeasure)^(5/3:ℝ)) ≤
      ∫ R, (∫ y, f R y^(5/3:ℝ)) ∂cubeRotationMeasure at hp
  simp_rw [hae] at hp
  refine ⟨hp.1,hp.2.trans ?_⟩
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun R => integral_nonneg (fun y => Real.rpow_nonneg (hn R y) _)))
    (translatedPressureAverage_rotation_integrable x)
    (Eventually.of_forall hb)

end CoulombNeumann
end
end OAI
