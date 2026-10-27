public section

open CategoryTheory

open scoped TensorProduct

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

namespace AInfinityRightModuleCat

attribute [instance] addCommGroup moduleBase

variable {AA : AInfinityAlgebra R A}

/-- Bundle a right `A∞` module with its existing module structures. -/
abbrev of {M : Type uM} [AddCommGroup M] [Module R M] (MM : AInfinityRightModule AA M) :
    AInfinityRightModuleCat AA where
  carrier := M
  str := MM

end AInfinityRightModuleCat
end TauCeti
end
