@[expose] public section

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

section OddCoprimeTower

variable (sigma : K) (hsigma : sigma ≠ 0) (e d : ℕ)
  (heOdd : Odd e) (hdOdd : Odd d) (hde : d.Coprime e)

theorem splitTraceLaurentToKummerTop_algebraMap_apply
    (a : SplitTraceAffineCoordinateRing K sigma d e) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    letI : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) :=
      ⟨splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd⟩
    letI : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) :=
      ⟨splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde⟩
    splitTraceLaurentToKummerTop sigma hsigma e d heOdd hdOdd hde
        (algebraMap (SplitTraceAffineCoordinateRing K sigma d e)
          (SplitTraceLaurentCoordinateRing K sigma d e) a) =
      splitTraceAffineToKummerTop sigma hsigma e d heOdd hdOdd hde a := by
  let hBaseIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hBaseIrred⟩
  let hEtaIrred := splitTraceEtaKummerPolynomial_irreducible' sigma hsigma e heOdd
  let : Fact (Irreducible (splitTraceEtaKummerPolynomial sigma e)) := ⟨hEtaIrred⟩
  let hXiIrred :=
    splitTraceXiKummerPolynomial_irreducible sigma hsigma e d heOdd hdOdd hde
  let : Fact (Irreducible (splitTraceXiKummerPolynomial sigma e d)) := ⟨hXiIrred⟩
  simp only [splitTraceLaurentToKummerTop, IsLocalization.Away.liftAlgHom_apply]
  apply IsLocalization.Away.lift_eq

end OddCoprimeTower
end
end BGS.Markoff
end
