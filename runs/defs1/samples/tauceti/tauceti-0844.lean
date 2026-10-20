public section

namespace TauCeti

universe uR uA uB uC

namespace AInfinityHom

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {CC : AInfinityAlgebra R C}

/-- The coaugmented bar map is a coalgebra morphism. -/
noncomputable def coaugmentedBarCoalgHom (f : AInfinityHom AA BB) :
    TensorWords R A →ₗc[R] TensorWords R B :=
  ReducedTensorWords.coaugmentedCoalgHom f.isCoalgHom_barMap

end AInfinityHom
end TauCeti
end
