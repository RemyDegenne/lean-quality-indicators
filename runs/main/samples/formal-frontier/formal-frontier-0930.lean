@[expose] public section

universe u v w u' v' w'

namespace Algebra.GrothendieckAddGroup

variable {A : Type u} {G : Type w} [AddCommMonoid A] [AddCommGroup G]

variable {B : Type v} [AddCommMonoid B]

theorem lift₂_unique (f : A →+ B →+ G)
    (g : GrothendieckAddGroup A →+ GrothendieckAddGroup B →+ G)
    (h : ∀ (a : A) (b : B), g (of a) (of b) = f a b) : lift₂ f = g := by
  apply hom_ext₂
  intro a b
  exact (lift₂_of f a b).trans (h a b).symm

end Algebra.GrothendieckAddGroup
end
