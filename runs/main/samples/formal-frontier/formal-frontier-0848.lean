@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι

variable {R : Type uR} {ι : Type uι} [CommRing R]

@[simp] theorem pointSquareZeroAlgEquiv_mk_none (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) :
    pointSquareZeroAlgEquiv a hsep
      (Ideal.Quotient.mk (pointSquareZeroIdeal a) (X none)) =
        TrivSqZeroExt.inl (Polynomial.X : R[X]) := by
  simpa only [pointSquareZeroAlgEquiv, AlgEquiv.ofBijective_apply] using
    pointSquareZeroForward_mk_none a

end MvPolynomial
end
