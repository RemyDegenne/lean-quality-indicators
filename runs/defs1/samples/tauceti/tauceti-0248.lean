public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C}

/-- An exact structure has enough injectives if every object admits a relative injective
presentation. -/
structure EnoughInjectives (E : ExactStructure C) : Prop where
  presentation : ∀ X : C, Nonempty (E.InjectivePresentation X)

end ExactStructure
end TauCeti
end
