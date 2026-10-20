@[expose] public section

namespace ToricIdeals.RationalNormalCurve

open MvPolynomial

noncomputable section

universe u v

/-- The finite coefficient-coordinate equivalence of the homogeneous quotient
submodule. Its inverse forms the corresponding linear combination of basis vectors. -/
def quotientHomogeneousCoordinates (R : Type u) [CommRing R] (n d : ℕ) :
    quotientHomogeneousSubmodule R n d ≃ₗ[R] (Fin (n * d + 1) → R) :=
  (quotientHomogeneousBasis R n d).equivFun

end
end ToricIdeals.RationalNormalCurve
end
