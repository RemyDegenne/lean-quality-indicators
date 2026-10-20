public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w'' v v' v'' u u' u''

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] [EssentiallySmall.{w'} D]

namespace ExactK0

variable {E : ExactStructure C} {E' : ExactStructure D}

section HomExt

variable {G : Type*} [AddMonoid G]

@[ext]
theorem hom_ext {f g : ExactK0 E →+ G} (h : ∀ X : C, f (of X) = g (of X)) : f = g :=
  PresentedK0.hom_ext h

end HomExt
end ExactK0
end TauCeti
end
