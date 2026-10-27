@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι

variable {R : Type uR} {ι : Type uι} [CommRing R]

/-- The polynomial point quotient as the canonical square-zero extension of
its evaluation summands, under pairwise unit differences. This equivalence is
the fixed generator-prescribed forward map. -/
noncomputable def pointSquareZeroAlgEquiv (a : ι → R)
    (hsep : ∀ i j : ι, i ≠ j → IsUnit (a i - a j)) :
    pointSquareZeroQuotient a ≃ₐ[R[X]]
      TrivSqZeroExt R[X] (pointSquareZeroModule a) :=
  AlgEquiv.ofBijective (pointSquareZeroForward a)
    (pointSquareZeroForward_bijective a hsep)

end MvPolynomial
end
