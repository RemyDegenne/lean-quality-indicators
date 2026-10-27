@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

/-- Polynomial extension by one further central variable as a functor on rings. -/
def polynomialFunctor : RingCat.{u} ⥤ RingCat.{u} where
  obj A := RingCat.of (Polynomial A)
  map phi := RingCat.ofHom (Polynomial.mapRingHom phi.hom)
  map_id A := by
    apply RingCat.hom_ext
    exact Polynomial.mapRingHom_id
  map_comp phi psi := by
    apply RingCat.hom_ext
    exact (Polynomial.mapRingHom_comp psi.hom phi.hom).symm

end
end CentralPolynomialSimplex
end
