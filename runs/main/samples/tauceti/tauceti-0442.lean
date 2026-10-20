public section

namespace TauCeti

open LaurentPolynomial TemperleyLieb

namespace OrientedPDCode

variable {n : ℕ}

section Injectivity

@[simp] theorem jonesPolynomial_insertCircleClasp (D : OrientedPDCode n)
    (p : Fin (4 * n)) (o b : Bool) :
    (D.insertCircleClasp p o b).jonesPolynomial = (D.adjoinCircle o).jonesPolynomial :=
  (jonesPolynomial_eq_jonesPolynomial_iff _ _).2
    (D.normalizedKauffmanBracket_insertCircleClasp p o b _)

end Injectivity
end OrientedPDCode
end TauCeti
end
