public section

open AlgebraicGeometry CategoryTheory WithConv

open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **Inner conjugation by the integral Weyl-word point**, as an automorphism of the Geck group
scheme. On points over a commutative ring it sends `g` to `n_l g n_l⁻¹`. -/
def geckWeylWordInnerConjugation (l : List (Fin t.rank)) : Aut (t.geckGroupScheme ht) :=
  t.geckInnerConjugation ht (t.geckWeylWordPoint ht l ℤ)

end
end TauCeti.DynkinType
end
