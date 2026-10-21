namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators

open MulChar AddChar

open scoped BigOperators

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped FourierTransform SchwartzMap

open Finset Complex

open scoped Classical

open scoped Classical

open Filter Real Asymptotics

open ActualEisensteinCubic

open Filter

open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

open ActualEisensteinCubic ShortDraftLatticeCount

open Filter

open scoped Topology

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

open Filter Asymptotics

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter

open MulChar AddChar

open MulChar AddChar

open scoped LSeries.notation ArithmeticFunction.Moebius

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

open Filter Asymptotics

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics Ideal NumberField

open Filter

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open Filter Asymptotics MeasureTheory

open scoped Topology

open MeasureTheory Real

open scoped ContDiff FourierTransform SchwartzMap

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory Set

open scoped BigOperators

open scoped BigOperators Classical

open scoped BigOperators Classical

open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical

open Filter MeasureTheory

open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups

open Filter MeasureTheory

open scoped BigOperators Classical Topology

open Filter MeasureTheory

open scoped BigOperators Classical Topology

lemma kernelEisensteinResolvent_analyticAt_of_isUnit (s : ℂ)
    (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_of_isUnit _ hs).comp_of_eq
    (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

end CubicEisenstein
end
end OAI
