public section

open CategoryTheory

open AlgebraicGeometry

namespace TauCeti

universe u

namespace SplitTorus

variable {R A sigma tau upsilon : Type u} [CommRing R] [CommRing A]

variable [Algebra R A] [Finite sigma] [Finite tau] [Finite upsilon]

/-- Convert an integral linear map between finite coordinate lattices into the corresponding
homomorphism of free multiplicative character groups. -/
noncomputable def characterMapOfLinearMap (f : (sigma → ℤ) →ₗ[ℤ] (tau → ℤ)) :
    Multiplicative (sigma →₀ ℤ) →* Multiplicative (tau →₀ ℤ) :=
  AddMonoidHom.toMultiplicative
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ tau).symm.toLinearMap.comp
      (f.comp (Finsupp.linearEquivFunOnFinite ℤ ℤ sigma).toLinearMap)).toAddMonoidHom

end SplitTorus
end TauCeti
end
