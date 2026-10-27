@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

/-- Functoriality of central-polynomial simplices in the coefficient ring. -/
def coefficientNatural {A B : RingCat.{u}} (phi : A ⟶ B) :
    simplex A ⟶ simplex B where
  app x := RingCat.ofHom (coefficientMap phi.hom x.unop.len)
  naturality := by
    intro x y f
    apply RingCat.hom_ext
    exact coefficientMap_ordinalMap phi.hom f.unop

end
end CentralPolynomialSimplex
end
