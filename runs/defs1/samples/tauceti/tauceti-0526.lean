public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Matrix-coefficient morphisms depend linearly on the functional. -/
def matrixCoefficientHomLinear :
    Module.Dual R M →ₗ[R] Hom R C M C where
  toFun := matrixCoefficientHom (C := C)
  map_add' := matrixCoefficientHom_add (C := C)
  map_smul' := matrixCoefficientHom_smul (C := C)

end TauCeti.Comodule
end
