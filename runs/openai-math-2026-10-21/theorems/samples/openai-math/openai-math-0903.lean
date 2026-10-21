namespace OAI

section

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter

open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_scalar_sub (a : ℝ) (V : HeatMat6)
    (hV : Vᵀ = V) (htrace : (twoFormHodgeMatrix * V).trace = 0) :
    heatSignedGram (a • 1 - V) (a • 1 - V) = (twoFormHodgeMatrix * V * V).trace := by
  unfold heatSignedGram
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hV]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    twoFormHodgeMatrix_trace, htrace, mul_zero, sub_zero, zero_sub, neg_neg]
  exact congrArg Matrix.trace (Matrix.mul_assoc twoFormHodgeMatrix V V).symm

end
end PositiveEinsteinFour.Geometry
end
end OAI
