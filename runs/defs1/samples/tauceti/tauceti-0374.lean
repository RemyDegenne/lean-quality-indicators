public section

namespace TauCeti

universe uR uA uB

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The cycles of an `A∞` algebra are the kernel of its unary operation. -/
def cycles (𝒜 : AInfinityAlgebra R A) : Submodule R A :=
  LinearMap.ker 𝒜.differential

end AInfinityAlgebra
end TauCeti
end
