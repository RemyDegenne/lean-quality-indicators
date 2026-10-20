public section

open Bundle

open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

theorem scalarCurvature_eq_sum_inner_curvatureTensor {i : Type*} [Fintype i] (x : M)
    (b : OrthonormalBasis i ℝ (TangentSpace I x)) :
    cov.scalarCurvature x =
      ∑ j, ∑ k, inner ℝ (b k) (curvature x (b k) (b j) (b j)) := by
  rw [scalarCurvature_eq_sum cov x b]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact ricciTensor_eq_sum_inner cov x b (b j) (b j)

end CovariantDerivative
end
end
