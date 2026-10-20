public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w w' w'' v v' v'' u u' u''

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]

section Functoriality

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
  [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D] [HasBinaryBiproducts D]
  [EssentiallySmall.{w'} D]

namespace SplitK0

lemma map_congr {F G : C ⥤ D} [F.PreservesZeroMorphisms]
    [PreservesBiproductsOfShape WalkingPair F] [G.PreservesZeroMorphisms]
    [PreservesBiproductsOfShape WalkingPair G]
    (h : ∀ X : C, Nonempty (F.obj X ≅ G.obj X)) : map F = map G :=
  PresentedK0.map_congr h _ _

end SplitK0
end Functoriality
end TauCeti
end
