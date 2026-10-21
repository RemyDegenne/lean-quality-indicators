namespace OAI

open MeasureTheory Set

open scoped ENNReal NNReal Topology ContDiff

open scoped RealInnerProductSpace

open MeasureTheory Set Filter

open scoped Topology ENNReal

open scoped Real RealInnerProductSpace

open MeasureTheory Set Filter

open scoped Topology RealInnerProductSpace ContDiff

open MeasureTheory Set Filter

open scoped Topology Interval NNReal

open MeasureTheory Set Filter

open scoped Topology NNReal Real

open MeasureTheory Set Metric

open scoped ENNReal NNReal Topology

open MeasureTheory Set

open scoped ENNReal NNReal

open MeasureTheory Set

open scoped ENNReal NNReal

open MeasureTheory Set

open scoped ENNReal NNReal Topology

open MeasureTheory Set Metric

open scoped ENNReal NNReal

open MeasureTheory Set

open scoped ENNReal NNReal

open Finset

open scoped RealInnerProductSpace

open MeasureTheory Set Metric

open scoped ENNReal NNReal Topology

open MeasureTheory Set

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace PlanePotential

theorem green_representation {ψ g : ℂ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hg : ContDiff ℝ 1 g) {D : ℝ}
    (hD : ∀ y, ‖fderiv ℝ g y‖ ≤ D) (hψ1 : ∫ z, ψ z = 1) (x : ℂ) :
    (∫ y, fderiv ℝ g y (green ψ x y)) = g x-∫ z, ψ z*g z := by
  have hseg := segmentForm_integrable hψ hψc hg hD x
  have hpull := pullbackForm_integrable hψ hψc hg hD x
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hψgi : Integrable (fun z => ψ z*g z) :=
    (hψ.mul hg.continuous).integrable_of_hasCompactSupport hψc.mul_right
  calc
    _ = -(∫ y, ∫ t in Ioc (0:ℝ) 1, pullbackForm ψ g x t y) := by
      simp_rw [green_pullback]; rw [integral_neg]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ y, pullbackForm ψ g x t y) := by
      rw [← integral_integral_swap hpull]
    _ = -(∫ t in Ioc (0:ℝ) 1, ∫ z, segmentForm ψ g x t z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact pullback_column_integral ψ g x ht.1
    _ = -(∫ z, ∫ t in Ioc (0:ℝ) 1, segmentForm ψ g x t z) := by
      rw [integral_integral_swap hseg]
    _ = -(∫ z, ψ z*(g z-g x)) := by
      simp_rw [segmentForm,integral_const_mul,segment_ftc hg]
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hψgi (hψi.mul_const _),integral_mul_const,hψ1]
      ring

end PlanePotential
end
end OAI
