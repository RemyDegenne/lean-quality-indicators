@[expose] public section

universe u v w u' v' w'

namespace Algebra.GrothendieckAddGroup

variable {A : Type u} {G : Type w} [AddCommMonoid A] [AddCommGroup G]

@[simp]
theorem lift_of (f : A →+ G) (a : A) : lift f (of a) = f a := by
  exact DFunLike.congr_fun ((lift (M := A) (G := G)).symm_apply_apply f) a

end Algebra.GrothendieckAddGroup
end
