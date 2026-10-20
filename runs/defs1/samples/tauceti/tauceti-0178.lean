public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ConflationClass

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]

/-- The category of conflations of a conflation class `E`. Its objects are distinguished short
complexes, and its morphisms are arbitrary morphisms of the underlying short complexes. -/
abbrev ConflationCategory (E : ConflationClass C) :=
  ObjectProperty.FullSubcategory (fun S : ShortComplex C ↦ E.Conflation S)

end ConflationClass
end TauCeti
end
