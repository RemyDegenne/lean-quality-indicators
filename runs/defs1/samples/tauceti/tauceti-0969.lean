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

namespace BiadditiveInvariant

variable (a : BiadditiveInvariant E E' G)

/-- Descend an object-level biadditive invariant through both exact Grothendieck groups. -/
noncomputable def bilift : ExactK0 E →+ ExactK0 E' →+ G :=
  lift a.leftInvariant

end BiadditiveInvariant
end ExactK0
end TauCeti
end
