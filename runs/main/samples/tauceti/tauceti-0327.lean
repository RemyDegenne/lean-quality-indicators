public section

namespace TauCeti

open CategoryTheory

universe w w' w'' v v' v'' u u' u''

section Functoriality

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w'} D]

variable {relsC : Set (FreeAbelianGroup (ObjectCode C))}
  {relsD : Set (FreeAbelianGroup (ObjectCode D))}

namespace PresentedK0

@[simp]
lemma map_mk (F : C ⥤ D) (h : ∀ r ∈ relsC, freeMap F r ∈ AddSubgroup.closure relsD)
    (r : FreeAbelianGroup (ObjectCode C)) : map F h (mk r) = mk (freeMap F r) :=
  QuotientAddGroup.map_mk _ _ _ _ _

end PresentedK0
end Functoriality
end TauCeti
end
