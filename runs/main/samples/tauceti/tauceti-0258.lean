public section

namespace TauCeti

open Module

namespace IsSimpleRing

section Simplicity

variable {R : Type*} [Ring R] [IsSimpleRing R] [IsArtinianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem moduleEnd [Nontrivial M] : IsSimpleRing (Module.End R M) :=
  isSimpleRing_moduleEnd_of_isIsotypic (_root_.IsSimpleRing.isIsotypic R M)

end Simplicity
end IsSimpleRing
end TauCeti
end
