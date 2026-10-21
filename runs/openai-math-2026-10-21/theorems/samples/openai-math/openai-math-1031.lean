namespace OAI

noncomputable section

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

open MeasureTheory

open scoped BigOperators Classical SchwartzMap ContDiff

namespace InitialMeanSquare

section

open ActualEisensteinCubic

open SecondPassArithmetic

theorem initial_source_target_coprime
    {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) [∀i,(Ideal.span {p i}).IsMaximal]
    (bad : Ideal ActualEisensteinCubic.O) (hbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (s : Finset (SecondExpansionData ι)) :
    ∀z∈sourceIdealTarget (s.image (sourceObservation p)),IsCoprime z.1 bad := by
  intro z hz
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
  change IsCoprime (Ideal.span {(sourceObservation p x).2}) bad
  rw [sourceLabel_span]
  exact (IsCoprime.prod_left (fun i _=>hbad i)).mul_left
    (IsCoprime.prod_left (fun i _=>hbad i))

end
end InitialMeanSquare
end
end OAI
