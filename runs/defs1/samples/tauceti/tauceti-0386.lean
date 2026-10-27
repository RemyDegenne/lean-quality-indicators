public section

open scoped TensorProduct

namespace TauCeti

section Map

variable {k L K A : Type*} [CommSemiring k] [CommSemiring L] [Algebra k L]
  [CommSemiring K] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
  [Semiring A] [Bialgebra k A]

/-- Extension of the coefficients of a character through a tower of scalar rings. -/
noncomputable def groupLikeScalarTowerHom :
    _root_.GroupLike L (L ⊗[k] A) →* _root_.GroupLike K (K ⊗[k] A) :=
  (GroupLike.mapEquiv (Bialgebra.TensorProduct.baseChangeTowerBialgEquiv k L A K)).toMonoidHom.comp
    groupLikeBaseChange

end Map
end TauCeti
end
