@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

section OddCoprime

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

theorem splitTraceCoverPolynomial_irreducible_of_laurentInjective
    (hLaurent : Function.Injective
      (splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde)) :
    Irreducible (splitTraceCoverPolynomial (1 : K) sigma d e) := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  let : IsDomain (SplitTraceXiFunctionField K sigma e d) :=
    AdjoinRoot.isDomain_of_prime hXiIrred.prime
  let I : Ideal (MvPolynomial (Fin 2) K) :=
    Ideal.span {splitTraceCoverPolynomial (1 : K) sigma d e}
  have hAffine := splitTraceAffineToKummerTop_injective_of_laurentInjective
    sigma hsigma e d heOdd hdOdd hde hLaurent
  let : IsDomain (SplitTraceAffineCoordinateRing K sigma d e) :=
    hAffine.isDomain
      (splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde).toRingHom
  have hprimeIdeal : I.IsPrime := by
    exact (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  have hprimeElement : Prime (splitTraceCoverPolynomial (1 : K) sigma d e) :=
    (Ideal.span_singleton_prime
      (splitTraceCoverPolynomial_ne_zero sigma e d hdOdd)).1 (by
        simpa [I] using hprimeIdeal)
  exact irreducible_iff_prime.mpr hprimeElement

end OddCoprime
end
end BGS.Markoff
end
