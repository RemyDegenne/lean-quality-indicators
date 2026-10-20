public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- The standard polynomial presentation of the additive-group coordinate ring. -/
@[expose] def additiveGroupCoordinateAlgEquiv
  (K : Type u) [CommRing K] :
    additiveGroupCoordinateRing K ≃ₐ[K] Polynomial K :=
  (SymmetricAlgebra.equivMvPolynomial (Module.Basis.singleton Unit K)).trans
    (MvPolynomial.uniqueAlgEquiv K Unit)

end AlgebraicGeometry
end
end
