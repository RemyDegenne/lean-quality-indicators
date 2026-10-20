@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

theorem quotientHomogeneousCoordinates_ext (R : Type u) [CommRing R] (n d : ℕ)
    {x y : quotientHomogeneousSubmodule R n d}
    (h : ∀ i, quotientHomogeneousCoordinates R n d x i =
      quotientHomogeneousCoordinates R n d y i) : x = y :=
  (quotientHomogeneousCoordinates R n d).injective (funext h)

end
end ToricIdeals.RationalNormalCurve
end
