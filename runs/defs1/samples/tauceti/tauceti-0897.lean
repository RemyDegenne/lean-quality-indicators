public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uB uC

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

namespace AInfinityHom

variable {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} {CC : AInfinityAlgebra R C}

/-- The map induced on cohomology by an `A∞` morphism, as a strict morphism of the cohomology `A∞`
algebras. -/
noncomputable def cohomologyStrictHom (f : AInfinityHom AA BB) :
    AInfinityStrictHom AA.cohomologyAInfinityAlgebra BB.cohomologyAInfinityAlgebra :=
  f.cohomologyMap.cohomologyStrictHom f.cohomologyMap_mem_cohomologyGrading_piece

end AInfinityHom
end TauCeti
end
