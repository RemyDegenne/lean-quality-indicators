@[expose] public section

universe uR uM uN uH uA uB

namespace MonoidAlgebra

variable {R : Type uR} {M : Type uM} {N : Type uN} {H : Type uH}

variable {A : Type uA} {B : Type uB}

section Bialgebra

variable [CommSemiring R] [Monoid M] [Semiring A] [Bialgebra R A]

theorem valMonoidHom_comp_groupLikeHomOfBialgHom (F : R[M] →ₐc[R] A) :
    (GroupLike.valMonoidHom R A).comp (groupLikeHomOfBialgHom F) =
      (lift R A M).symm F.toAlgHom := by
  rfl

end Bialgebra
end MonoidAlgebra
end
