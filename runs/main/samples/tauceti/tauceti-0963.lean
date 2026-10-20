public section

noncomputable section

namespace TauCeti.NodeAlgebra

open MvPolynomial

variable {R : Type*} [CommRing R] (a : R)

variable {M : Type*} [AddCommMonoid M] [Module (NodeAlgebra R a) M]
  [Module R M] [IsScalarTower R (NodeAlgebra R a) M]

@[simp]
lemma derivationEquivValues_apply (D : Derivation R (NodeAlgebra R a) M)
    (i : Fin 2) : (derivationEquivValues a D).1 i = D (coord a i) := by
  rfl

end TauCeti.NodeAlgebra
end
end
