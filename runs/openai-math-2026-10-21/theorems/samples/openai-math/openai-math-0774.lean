namespace OAI

noncomputable section

open MeasureTheory Set

open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

open MeasureTheory Set Filter

open scoped ENNReal NNReal

open MeasureTheory Set Filter

open scoped ENNReal NNReal

open MeasureTheory Set

open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

open MeasureTheory Set

open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set

open scoped BigOperators ENNReal ContDiff

open MeasureTheory Set Filter

open scoped ENNReal NNReal ContDiff

open MeasureTheory Set Filter

open scoped ENNReal NNReal ContDiff

open scoped Classical

open scoped BigOperators ComplexConjugate

open scoped Classical

open scoped Classical

open MeasureTheory Set Filter

open scoped Classical ENNReal NNReal ComplexConjugate

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function

open scoped Classical ComplexConjugate

open MeasureTheory Set Filter Module Module.End TopologicalSpace Function

open scoped Classical ComplexConjugate

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

open MeasureTheory Set Filter

open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

open MeasureTheory Filter

open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate

open scoped LineDeriv

open MeasureTheory Set Metric

open scoped ENNReal NNReal RealInnerProductSpace

open MeasureTheory Set Metric Filter

open scoped ENNReal NNReal RealInnerProductSpace Convolution

open MeasureTheory Set Filter

open scoped ENNReal NNReal ComplexConjugate

open MeasureTheory Set Filter

open scoped ENNReal NNReal ContDiff

open MeasureTheory Set Filter

open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise

open MeasureTheory Set Filter

open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

open MeasureTheory Set Filter

open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

open MeasureTheory Set Filter

open scoped Classical SchwartzMap ENNReal NNReal Pointwise

open MeasureTheory Set Filter

open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

open MeasureTheory Set Filter

open scoped ENNReal NNReal Classical SchwartzMap Pointwise

open MeasureTheory Set Filter

open scoped ENNReal NNReal Classical SchwartzMap Pointwise

open MeasureTheory Set Filter

open scoped ENNReal NNReal Classical SchwartzMap Pointwise

open MeasureTheory Set Filter

open scoped ENNReal NNReal Classical SchwartzMap Pointwise

open MeasureTheory Set Filter

open scoped ENNReal NNReal Classical SchwartzMap Pointwise

open MeasureTheory Set Filter

open scoped ENNReal NNReal Classical SchwartzMap Pointwise

open MeasureTheory Set

open scoped BigOperators ENNReal

namespace Coulomb

open scoped Classical

open scoped Classical

open Filter

open scoped Convolution

open ContinuousLinearMap

lemma finiteCubeMeasure_real_univ {b : ℝ} (hb : 0 < b) (I : Type*) [Fintype I] :
    (finiteCubeMeasure b I).real univ = b ^ Fintype.card I := by
  simp [Measure.real, finiteCubeMeasure, Measure.pi_univ, hb.le]

end Coulomb
end
end OAI
