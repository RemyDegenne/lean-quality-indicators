namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder

open Filter

open scoped BigOperators

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

open scoped InnerProductSpace ComplexConjugate

open Filter Topology

open Filter Set Topology

open scoped InnerProductSpace ComplexConjugate Topology

open scoped InnerProductSpace

open scoped BigOperators Topology InnerProductSpace

open scoped BigOperators InnerProductSpace

open scoped BigOperators Matrix Topology ComplexConjugate

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology

open scoped BigOperators Matrix Topology

open scoped BigOperators Matrix Topology Matrix.Norms.Operator

open scoped Topology

open Filter Asymptotics

open scoped InnerProductSpace Topology

open scoped InnerProductSpace BigOperators

open scoped InnerProductSpace Topology BigOperators

open scoped Topology BigOperators

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators

open Filter ContinuousLinearMap

open ContinuousLinearMap

open scoped InnerProductSpace BigOperators Topology

open ContinuousLinearMap InnerProductSpace

open ContinuousLinearMap Filter

open Filter MeasureTheory

open scoped Topology ENNReal

open MeasureTheory ProbabilityTheory

open scoped BigOperators Topology RealInnerProductSpace

open scoped BigOperators TensorProduct

open scoped Topology InnerProductSpace

open MeasureTheory Filter

open MeasureTheory ProbabilityTheory Complex

open scoped BigOperators Topology InnerProductSpace ComplexConjugate

open scoped BigOperators Topology NNReal

open scoped BigOperators NNReal Topology

open scoped BigOperators NNReal

open scoped NNReal Topology

open scoped NNReal Topology BigOperators

open MeasureTheory ProbabilityTheory Filter TopologicalSpace

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter TopologicalSpace

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter TopologicalSpace

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace

open scoped BigOperators Topology NNReal ENNReal

namespace SKCavity

open SKQAOA SKGaussian ParisiInterpolation

lemma overlapTails_measurable {S : Set OverlapEntry} (hS : S∈overlapTails) : MeasurableSet S := by
  obtain ⟨t,rfl⟩ := hS
  exact measurableSet_lt measurable_const (by fun_prop)

end SKCavity
end
end OAI
