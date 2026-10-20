@[expose] public section

noncomputable section

namespace EulerMeanSolenoidal

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerCoerciveProjection
  EulerLiftedPressure

open scoped ContDiff ENNReal NNReal

section ClassicalFields

open EulerVectorCalculus

theorem gradient_test_integration_by_parts (u : Space → Space)
    (hu : ContDiff ℝ ∞ u) (φ : Space → ℝ)
    (hc : HasCompactSupport φ) (hs : ContDiff ℝ ∞ φ) :
    (∫ x, ⟪gradient φ x, u x⟫_ℝ) = -∫ x, φ x * divergence u x := by
  let ui (i : Fin 3) (x : Space) := u x i
  have hui (i : Fin 3) : ContDiff ℝ ∞ (ui i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hu
  have hi₁ (i : Fin 3) : Integrable (fun x => partialDerivative φ i x * ui i x) :=
    ((contDiff_partialDerivative φ hs i).continuous.mul (hui
        i).continuous).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_right)
  have hi₂ (i : Fin 3) : Integrable (fun x => φ x * partialDerivative (ui i) i x) :=
    (hs.continuous.mul (contDiff_partialDerivative _ (hui i)
        i).continuous).integrable_of_hasCompactSupport
      hc.mul_right
  have hibp (i : Fin 3) : (∫ x, partialDerivative φ i x * ui i x) =
      -∫ x, φ x * partialDerivative (ui i) i x := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure Space)) (v := EuclideanSpace.single i 1)
      (hi₁ i) (hi₂ i)
      ((hs.continuous.mul (hui i).continuous).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ => (hs.differentiable (by simp)).differentiableAt)
      (fun x _ => ((hui i).differentiable (by simp)).differentiableAt)
    change (∫ x, φ x * partialDerivative (ui i) i x) =
      -∫ x, partialDerivative φ i x * ui i x at h
    linarith
  have hinner (x : Space) : ⟪gradient φ x, u x⟫_ℝ =
      ∑ i : Fin 3, partialDerivative φ i x * ui i x := by
    rw [inner_gradient_left]
    have hre : ∑ i : Fin 3, u x i • (EuclideanSpace.single i 1 : Space) = u x := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (u x)
    calc
      fderiv ℝ φ x (u x) =
          fderiv ℝ φ x (∑ i : Fin 3, u x i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ φ x) hre.symm
      _ = ∑ i : Fin 3, partialDerivative φ i x * ui i x := by
        simp only [map_sum, map_smul, smul_eq_mul, partialDerivative, ui, mul_comm]
  have hdiv (x : Space) : φ x * divergence u x =
      ∑ i : Fin 3, φ x * partialDerivative (ui i) i x := by
    rw [divergence_eq_coordinate_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (fderiv_coordinate u x ((hu.differentiable (by simp)).differentiableAt)
      i (EuclideanSpace.single i 1)).symm
  simp_rw [hinner, hdiv]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),
    integral_finsetSum _ (fun i _ => hi₂ i)]
  simp only [hibp, Finset.sum_neg_distrib]

end ClassicalFields
end EulerMeanSolenoidal
end
end
