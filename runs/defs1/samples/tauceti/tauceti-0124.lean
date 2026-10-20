public section

namespace TauCeti

open MulOpposite

variable (k A P N : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommMonoid P] [Module A P]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

variable {P N}

variable (P N)

/-- The canonical tensor–Hom equivalence for a finite projective left module.
The tensor product uses the opposite dual and is balanced over `A`. -/
noncomputable def balancedDualTensorHomEquiv [Module.Finite A P] [Module.Projective A P] :
    BalancedTensorProduct k A (Module.Dual A P) N ≃ₗ[k] (P →ₗ[A] N) :=
  LinearEquiv.ofBijective (balancedDualTensorHom k A P N)
    (balancedDualTensorHom_bijective k A)

end TauCeti
end
