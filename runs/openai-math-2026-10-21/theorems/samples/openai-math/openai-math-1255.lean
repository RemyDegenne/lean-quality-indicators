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

namespace CubicEisenstein

section

open scoped BigOperators Classical

open MeasureTheory

open Finset AddChar MulChar EisensteinEmbedding

section

local notation "Eis" => ActualEisensteinCubic.O

theorem finiteConjugateSource_wirtingerBar {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (finiteConjugateSource shift weight v hv) z=
      ∑'h : Eis,(-2*Real.pi*Complex.I*star (cuspFrequency h))*
        (∑i,weight i*ShortDraftTrace.breveE (-cuspFrequency h*shift i))*
          star (sourceBesselCoefficients.term h (v,z)) := by
  have hf : finiteConjugateSource shift weight v hv = fun z=>
      star ((sourceBesselCoefficients.finiteTranslate shift (fun i=>star (weight i))).fullFunction
        ((∑i,star (weight i))*((3*(Real.pi:ℂ))*constantArithmeticResidue)) (upperPoint z v hv)) :=
    funext (finiteConjugateSource_eq_bessel shift weight v hv)
  rw [hf,horizontalWirtingerBar_star,
    SubexponentialBesselCoefficients.fullFunction_wirtingerZ,tsum_star]
  apply tsum_congr
  intro h
  rw [finiteTranslate_term_multiplier,star_mul,star_mul,finiteTranslationMultiplier_star]
  have hphase : star (2*Real.pi*Complex.I*cuspFrequency h)=
      -2*Real.pi*Complex.I*star (cuspFrequency h) := by
    simp only [star_mul,Complex.star_def,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
    ring
  rw [hphase]
  ring

end
end
end CubicEisenstein
end
end OAI
