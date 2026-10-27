public section

open scoped TensorProduct BigOperators

namespace TauCeti

universe uR uA uM uN uP

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {AA : AInfinityAlgebra R A}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

attribute [local instance] Comodule.cofree

namespace AInfinityRightModuleHom

variable {MM : AInfinityRightModule AA M} {NN : AInfinityRightModule AA N}
  {PP : AInfinityRightModule AA P}

/-- The linear part is the arity-one Taylor component, evaluated on the empty algebra word. -/
noncomputable def linearPart (f : AInfinityRightModuleHom MM NN) : M →ₗ[R] N :=
  f.taylor ∘ₗ (TensorProduct.mk R M (TensorWords R A)).flip 1

end AInfinityRightModuleHom
end TauCeti
end
