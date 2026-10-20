public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (V : Type u) [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

variable (R : Type u) [CommRing R] [Algebra K R]

/-- Tensor-valued points are the convolution group of algebra maps out of the
dual symmetric algebra. -/
@[expose] def vectorGroupMulEquivAlgHom :
    Multiplicative (V ⊗[K] R) ≃*
      WithConv (vectorGroupCoordinateRing K V →ₐ[K] R) :=
  (vectorGroupTensorDualEquiv K V R).toAddEquiv.toMultiplicative.trans
    (SymmetricAlgebra.linearMapMulEquivAlgHom K (Module.Dual K V) R)

end AlgebraicGeometry
end
end
