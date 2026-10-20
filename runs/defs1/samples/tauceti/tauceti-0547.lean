public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule TensorProduct

attribute [local instance] TauCeti.moduleNNRat

attribute [local instance high] Algebra.toModule

universe v w

variable {L : Type v} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra.IsKilling ℚ L]
  [FiniteDimensional ℚ L] {H : LieSubalgebra ℚ L} [H.IsCartanSubalgebra]
  [LieModule.IsTriangularizable ℚ H L]

namespace IsChevalleySystem

variable {ω : L ≃ₗ⁅ℚ⁆ L} {x : Weight ℚ H L → L} (hx : IsChevalleySystem ω x)

include hx

section Torus

/-- **The diagonal coroot-parameter torus action on the Chevalley lattice.** Over any commutative
ring `A` it acts on `A ⊗[ℤ] L_ℤ`, scaling the base-changed weight-basis vector `b i` by the value at
`s` of its character `chevalleyWeightFin i`.

The parameter is indexed by all weights of `L` rather than by the roots alone; at the zero weight
the coroot vanishes, and with it both the cocharacter
(`TauCeti.corootFamily_eq_zero_of_isZero`) and the weights of the generators
(`TauCeti.rootCartanWeight_eq_zero_of_isZero`). This is not the maximal torus of a pinning:
exhibiting that needs a rank-`ℓ` cocharacter datum, equivalently the simply connected
lattice, which the adjoint lattice does not supply. -/
noncomputable def chevalleyTorusPoints (A : Type*) [CommRing A] [Algebra ℤ A] :
    (Weight ℚ H L → Aˣ) →*
      LinearMap.GeneralLinearGroup A (A ⊗[ℤ] (rootCorootSpan x).toAddSubgroup) :=
  UniversalEnvelopingAlgebra.kostantTorusPoints (rootCorootSpan x).toAddSubgroup
    hx.chevalleyWeightBasisFin hx.chevalleyWeightFin A

end Torus
end IsChevalleySystem
end TauCeti
end
