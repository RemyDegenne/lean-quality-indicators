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

variable {G : Type*} [AddCommGroup G]

section Functoriality

variable (F : C ⥤ D) [F.Additive]

/-- **Functoriality of exact `K₀`**: a conflation-exact functor induces a homomorphism of exact
Grothendieck groups. -/
noncomputable def map (hF : E.IsConflationExact E' F) : ExactK0 E →+ ExactK0 E' :=
  PresentedK0.map F (mapsTo_exactRelations F hF)

end Functoriality
end ExactK0
end TauCeti
end
