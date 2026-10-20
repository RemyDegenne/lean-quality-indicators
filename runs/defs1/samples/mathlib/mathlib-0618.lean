@[expose] public section

universe v v' u u'

namespace CategoryTheory.Limits

section NonSmall

variable {C : Type u} [Category.{v} C]

/-- A presheaf is called an ind-object if it can be written as a filtered colimit of representable
presheaves. -/
structure IsIndObject (A : Cᵒᵖ ⥤ Type v) : Prop where
  mk' :: nonempty_presentation : Nonempty (IndObjectPresentation A)

end NonSmall
end CategoryTheory.Limits
end
