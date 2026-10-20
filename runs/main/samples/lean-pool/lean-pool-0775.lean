open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

public
theorem Smale.PartialChart.bijective_mfderiv {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    (Φ : PartialDiffeomorph I J M N ∞) {x : M} (hx : x ∈ Φ.source) :
    Function.Bijective (mfderiv I J Φ x) := by
  have hdiff : Φ.toOpenPartialHomeomorph.MDifferentiable I J :=
    ⟨Φ.mdifferentiableOn (by simp), Φ.symm.mdifferentiableOn (by simp)⟩
  exact hdiff.mfderiv_bijective hx

end Mathoverflow1973
end
