@[expose] public section

universe u v w

namespace GroupLike

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Semiring B]

variable [HopfAlgebra R A] [HopfAlgebra R B]

theorem toUnits_comp_groupLikeMap (f : A →ₐc[R] B) :
    (GroupLike.toUnits R (A := B)).comp f.groupLikeMap =
      (Units.map f.toAlgHom.toMonoidHom).comp (GroupLike.toUnits R (A := A)) := by
  apply MonoidHom.ext
  intro g
  exact toUnits_groupLikeMap f g

end GroupLike
end
