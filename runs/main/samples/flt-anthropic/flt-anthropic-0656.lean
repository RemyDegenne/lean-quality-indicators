namespace P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option maxHeartbeats 3200000

open MeasureTheory Real Complex Set TopologicalSpace Topology Submodule WithLp

open scoped FourierTransform InnerProductSpace

noncomputable section

namespace PiPoissonSummation

variable {d : Type*} [Fintype d]

theorem periodize_eq_tsum_piFourierIntegral (f : C((d → ℝ), ℂ))
    (hf : ∀ K : Compacts (d → ℝ),
      Summable fun n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖)
    (hf_int : Integrable (⇑f) (volume : Measure (d → ℝ)))
    (hFf : Summable fun m : d → ℤ => piFourierIntegral f (intVec m))
    (x : d → ℝ) :
    periodize f x
      = ∑' m : d → ℤ, piFourierIntegral f (intVec m)
          * UnitAddTorus.mFourier m (toUnitAddTorus x) := by
  set F := periodizeLift f hf
  rw [← periodizeLift_toUnitAddTorus f hf x]
  have hcoeff : ∀ m, UnitAddTorus.mFourierCoeff F m = piFourierIntegral f (intVec m) :=
    mFourierCoeff_eq_piFourierIntegral f hf hf_int F (periodizeLift_toUnitAddTorus f hf)
  have hsum : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine hFf.congr fun m => ?_
    exact (hcoeff m).symm
  have := (UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum
    (toUnitAddTorus x)).tsum_eq
  rw [← this]
  refine tsum_congr fun m => ?_
  rw [hcoeff m, smul_eq_mul]

end PiPoissonSummation
end
end P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace
