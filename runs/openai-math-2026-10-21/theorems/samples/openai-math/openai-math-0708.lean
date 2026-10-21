namespace OAI

noncomputable section

open MeasureTheory Filter FourierTransform

open scoped Topology ENNReal

namespace WeakPureInfiniteness

open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : StandardModularData H)

lemma modularNormalAdjointRegularized_mem (a : H →L[ℂ] H) (ha : a ∈ S.M)
    (g : BoundedContinuousFunction ℝ ℂ) (n : ℕ) :
    modularNormalAdjointRegularized S a g n ∈ modularCrossedProduct (volume : Measure ℝ) S :=
  mul_mem (modularNormalAdjoint_mem S a ha g) (modularTranslationCalculus_mem S _)

end WeakPureInfiniteness
end
end OAI
