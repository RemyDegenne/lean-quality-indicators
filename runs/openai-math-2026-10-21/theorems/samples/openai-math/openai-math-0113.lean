namespace OAI

open MeasureTheory Set

open scoped ENNReal symmDiff

noncomputable section

open MeasureTheory Set Filter Function Metric

open scoped Topology Convolution ContDiff

noncomputable section

namespace TriangularBilliards

open SpatialSmoothing

namespace Triangle

lemma reconstruct_difference (Q : Triangle) (x : ℂ) (k : Fin 3) :
    x - Q.vertex k = ∑ j : Fin 3, Q.basis.coord j x • (Q.vertex j - Q.vertex k) := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    Q.basis.sum_coord_apply_eq_one, one_smul]
  have h := Q.basis.linear_combination_coord_eq_self x
  change ∑ i, Q.basis.coord i x • Q.vertex i = x at h
  rw [h]

end Triangle
end TriangularBilliards
end
end
end OAI
