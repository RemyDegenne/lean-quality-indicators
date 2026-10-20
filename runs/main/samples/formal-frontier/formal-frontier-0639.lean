@[expose] public section

universe u v w u' v' w'

namespace Algebra.GrothendieckAddGroup

variable {A : Type u} {G : Type w} [AddCommMonoid A] [AddCommGroup G]

variable {B : Type v} [AddCommMonoid B]

theorem lift₂_compr₂ {H : Type w'} [AddCommGroup H]
    (f : A →+ B →+ G) (h : G →+ H) :
    lift₂ (f.compr₂ h) = (lift₂ f).compr₂ h := by
  apply hom_ext₂
  intro a b
  simp only [lift₂_of, AddMonoidHom.compr₂_apply]

end Algebra.GrothendieckAddGroup
end
