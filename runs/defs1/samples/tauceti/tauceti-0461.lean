public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace ExactStructure

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ConflationCategory

variable {E : ExactStructure C}

section Functor

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]

variable {E' : ExactStructure D} {F G : Functor C D}

/-- The functor on conflations induced by the identity functor is naturally isomorphic to the
identity functor. -/
abbrev mapIdIso : map (ExactStructure.IsConflationExact.id (E := E)) ≅
    Functor.id E.ConflationCategory :=
  ConflationClass.ConflationCategory.mapIdIso

end Functor
end ConflationCategory
end ExactStructure
end TauCeti
end
