namespace OAI

noncomputable section

open scoped Topology

open Filter

open Filter MeasureTheory

open UniformSpace

open scoped ContDiff

open UniformSpace

open Filter

open scoped Topology

open Filter MeasureTheory

open scoped Topology

namespace StronglyRationalVOA.SymmetricOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeAverage_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) :
    IsSelfAdjoint (timeAverage T hs r) := by
  change star (timeAverage T hs r) = timeAverage T hs r
  rw [timeAverage,star_smul,star_trivial]
  change (2*r)⁻¹ • (timeIntegral T hs (-r) r).adjoint = _
  rw [timeIntegral_adjoint,neg_neg]

end StronglyRationalVOA.SymmetricOperator
end
end OAI
