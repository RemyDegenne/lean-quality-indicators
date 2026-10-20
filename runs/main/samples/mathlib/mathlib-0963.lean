@[expose] public section

open MonoidAlgebra

open LinearMap Module

namespace Representation

section MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

variable (ρ : Representation k G V)

@[simp]
theorem asAlgebraHom_single (g : G) (r : k) :
    asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g := by
  simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]

end MonoidAlgebra
end Representation
end
