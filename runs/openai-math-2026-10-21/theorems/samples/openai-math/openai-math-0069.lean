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

open scoped Classical BigOperators

open scoped BigOperators Classical

namespace CompletedGauss

open ActualEisensteinCubic CanonicalQuadraticSieve

local notation "Eis" => ActualEisensteinCubic.O

theorem reconstructFiberRow_valid_iff (rows:Finset (Ideal Eis)) (I Q:Ideal Eis) (K:ℝ)
    (hbad:∀P∈fixedBadPrimes,P∣Q)
    (hrows:∀J∈rows,J≠0 ∧ (Ideal.absNorm J:ℝ)≤K)
    (k:idealRange (completedResidualScale K I Q)) :
    reconstructFiberRow I Q k.val∈representativeRowFiber rows I Q ↔
      ∃J:representativeRowFiber rows I Q,fiberResidualIndex rows I Q K hbad hrows J=k := by
  constructor
  · intro hk
    refine ⟨⟨reconstructFiberRow I Q k.val,hk⟩,?_⟩
    apply Subtype.ext
    exact residual_reconstructFiberRow rows I Q k.val (mem_idealRange.mp k.property).1.1 hk
  · rintro ⟨J,rfl⟩
    have hJ0:J.val≠0:=(hrows J.val (Finset.mem_filter.mp J.property).1).1
    change reconstructFiberRow I Q (rowResidualPart J.val Q)∈representativeRowFiber rows I Q
    rw [reconstructFiberRow_of_original rows I Q J.val J.property hJ0]
    exact J.property

end CompletedGauss
end
end OAI
