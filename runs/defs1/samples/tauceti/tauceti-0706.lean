public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- A bundled right `A∞` module over `AA`. -/
structure AInfinityRightModuleCat (AA : AInfinityAlgebra R A) where
  /-- The underlying module carrier. -/
  carrier : Type uM
  [addCommGroup : AddCommGroup carrier]
  [moduleBase : Module R carrier]
  /-- The right `A∞` module structure on the carrier. -/
  str : AInfinityRightModule AA carrier

end TauCeti
end
