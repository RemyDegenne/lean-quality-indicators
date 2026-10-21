namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

open Finset Real

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real Filter

open scoped Topology

namespace CriticalSK

section

lemma centeredChiRow_mean (n i : ℕ) : (∫ ω, centeredChiRow n i ω ∂chiRowLaw n) = 0 := by
  let f (x : Fin (chiRowDim n i) → ℝ) := chi (chiRowDim n i) x -
    ∫ y, chi (chiRowDim n i) y ∂standardGaussianProduct (chiRowDim n i)
  have he := integral_map (μ := chiRowLaw n) (φ := fun ω : ChiRows n => ω i)
    (f := f) (measurable_pi_apply i).aemeasurable
    ((chi_measurable _).sub measurable_const).aestronglyMeasurable
  change (∫ ω, f (ω i) ∂chiRowLaw n) = 0
  rw [← he]
  simp only [chiRowLaw, Measure.infinitePi_map_eval]
  dsimp only [f]
  rw [integral_sub (chi_integrable _) (integrable_const _)]
  simp

end
end CriticalSK
end
end OAI
