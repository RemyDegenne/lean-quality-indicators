@[expose] public section

universe uR uC uG

open scoped TensorProduct

namespace MonoidAlgebra

variable {R : Type uR} {C : Type uC} {G : Type uG}

section Ext

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

@[ext]
theorem coalgHom_ext {F H : R[G] →ₗc[R] C}
    (h : ∀ g, F (single g 1) = H (single g 1)) : F = H := by
  apply CoalgHom.coe_linearMap_injective
  exact lhom_ext' fun g => LinearMap.ext_ring (h g)

end Ext
end MonoidAlgebra
end
