@[expose] public section

open scoped TrivSqZeroExt Polynomial DirectSum

namespace MvPolynomial

universe uR uι uB

variable {R : Type uR} {ι : Type uι} [CommRing R]

/-- The square-zero point relations on the distinguished coordinate `none` and
the indexed coordinates `some i`. There are no mixed-product generators. -/
noncomputable def pointSquareZeroIdeal (a : ι → R) : Ideal (MvPolynomial (Option ι) R) :=
  Ideal.span (Set.range (fun i : ι => (X (some i) : MvPolynomial (Option ι) R) ^ 2) ∪
    Set.range (fun i : ι =>
      (X none - C (a i)) * (X (some i) : MvPolynomial (Option ι) R)))

end MvPolynomial
end
