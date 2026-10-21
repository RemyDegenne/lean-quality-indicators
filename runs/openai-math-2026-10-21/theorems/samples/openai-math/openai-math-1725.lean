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

open scoped BigOperators Classical

namespace CompletedGauss

section

open ActualEisensteinCubic LocalReflectionBrackets

local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance reflectionWeightField (P:Ideal Eis) [P.IsMaximal] : Field (Eis⧸P) :=
  Ideal.Quotient.field P

noncomputable local instance reflectionWeightFintype (P:Ideal Eis) [P.IsMaximal] : Fintype (Eis⧸P) :=
  Fintype.ofFinite _

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

theorem sum_reflectionSixWeight_unpad (P:ι→Ideal Eis) [∀i,(P i).IsMaximal]
    (hg:∀i,lambda∉P i) (j:ι→ℕ)
    (ψ:Finset ι→∀i,AddChar (Eis⧸P i) ℂ)
    (σ ε:Finset ι→∀i,(Eis⧸P i)ˣ) (G:(ι→Fin 6)→ℂ) :
    (∑e:ι→Fin 6,reflectionSixWeight P hg j ψ σ ε e*G e)=
      ∑A:Finset ι,∑e:A→Fin 3,reflectionStratumWeight P hg j ψ σ ε A*
        G (encodeReflectionSix ⟨A,e⟩) := by
  rw [sum_reflectionStratumWeight_eq_six]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he:reflectionSixValid e
  · rw [encode_decodeReflectionSix e he]
  · simp only [reflectionSixWeight,ite_eq_right he,zero_mul]

end
end CompletedGauss
end
end OAI
