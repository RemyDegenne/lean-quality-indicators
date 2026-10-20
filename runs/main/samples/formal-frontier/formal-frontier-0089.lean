@[expose] public section

universe u v w x

namespace BialgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type x}

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]

variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

@[simp]
theorem groupLikeMap_val (f : A →ₐc[R] B) (g : GroupLike R A) :
    (f.groupLikeMap g).val = f g.val := rfl

end BialgHom
end
