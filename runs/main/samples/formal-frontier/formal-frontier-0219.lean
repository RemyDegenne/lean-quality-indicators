@[expose] public section

universe u

namespace ToricIdeals.RationalNormalCurve

variable (R : Type u) [CommRing R] (n : ℕ)

@[simp] theorem quotientMap_X (i : Fin (n + 1)) :
    quotientMap R n (Ideal.Quotient.mk (hankelIdeal R n) (MvPolynomial.X i)) =
      MvPolynomial.monomial (coordinateExponent n i) 1 := by
  rw [quotientMap_mk, rncMap_X]

end ToricIdeals.RationalNormalCurve
end
