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

namespace ShortDraftCusp

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase

open CompletedGauss LocalReflectionBrackets

local notation "Eis" => ActualEisensteinCubic.O

noncomputable local instance A4frequencyField (P : Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

noncomputable local instance A4frequencyFintype (P : Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

theorem A3_A4_frequency_product {ι : Type*} [Fintype ι] (p : ι→Eis)
    [∀i,(Ideal.span {p i}).IsMaximal] (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (a b c0 d U w x:Eis) (hc0:c0≠0)
    (hdet:a*d-b*(c0*∏i,p i)=1)
    (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1)
    (σ ε : ∀i,(Eis⧸Ideal.span {p i})ˣ) (h : ∀i,Eis⧸Ideal.span {p i})
    (ha : ∀i,Ideal.Quotient.mk (Ideal.span {p i}) a=(σ i:Eis⧸Ideal.span {p i})*h i)
    (hε : ∀i,Ideal.Quotient.mk (Ideal.span {p i})
      (ramifiedTraceLambda^3*c0*cofactor p i)*(σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1) :
    star (eisEmbedding (CubicJacobiGlobal.symbol a (∏i,p i)))*
      ShortDraftTrace.breveE (-(eisEmbedding d*(eisEmbedding x/eisLam^4))/
        (eisEmbedding c0*eisEmbedding (∏i,p i))) =
    A4BadPhase c0 hc0 d U x *
      ∏i,frequencyMultiplier (actualSextic (Ideal.span {p i}) (hg i))
        (quotientTrace (p i) (hp i)) (σ i) (ε i) (Ideal.Quotient.mk _ x) (h i) := by
  rw [conjugate_symbol_product_frequency p hg a σ h ha,
    A4_phase_product p hp hcop a b c0 d U w x hc0 hdet hbez σ ε h ha hε]
  calc
    _ = A4BadPhase c0 hc0 d U x *
      ((∏i,(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        ((σ i:Eis⧸Ideal.span {p i})*h i))*
       ∏i,quotientTrace (p i) (hp i)
        (((ε i:Eis⧸Ideal.span {p i})*Ideal.Quotient.mk _ x)*(h i)⁻¹)) := by ring
    _ = _ := by
      congr 1
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      have hn:=(A4_active_local p a b c0 d hdet σ ε h ha hε x i).1
      simp only [frequencyMultiplier,ite_eq_right hn]

end ShortDraftCusp
end
end OAI
