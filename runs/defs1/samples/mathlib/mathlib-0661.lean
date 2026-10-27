@[expose] public section

universe u u' v v' w w'

namespace NonUnitalAlgebra

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

section IsScalarTower

variable [IsScalarTower R A A] [SMulCommClass R A A]

variable {R}

/-- Galois insertion between `adjoin` and `SetLike.coe`. -/
protected def gi : GaloisInsertion (adjoin R : Set A → NonUnitalSubalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (NonUnitalAlgebra.gc.le_u_l s) hs
  gc := NonUnitalAlgebra.gc
  le_l_u S := (NonUnitalAlgebra.gc (S : Set A) (adjoin R S)).1 le_rfl
  choice_eq _ _ := NonUnitalSubalgebra.copy_eq _ _ _

end IsScalarTower
end NonUnitalAlgebra
end
