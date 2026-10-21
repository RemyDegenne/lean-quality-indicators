namespace OAI

section

noncomputable section

open scoped BigOperators Matrix

open MeasureTheory ProbabilityTheory Set

namespace SK.Analytic

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

@[simp] theorem tripleRetainedEmbedding_apply (δ : ℝ) (x : TripleRetainedState) :
    tripleRetainedEmbedding δ x=![x.1.1,x.2+δ*x.1.2,x.2-δ*x.1.2] := by
  funext i; fin_cases i <;> rfl

end SK.Analytic
end
end
end OAI
