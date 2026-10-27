public section

noncomputable section

open CategoryTheory TensorProduct

open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K]

section End

variable (V : Type u) [AddCommGroup V] [Module K V]

variable [FiniteDimensional K V]

/-- The additive group comparison for finite-dimensional endomorphisms. -/
@[expose] def endVectorMulEquiv (R : Type u) [CommRing R] [Algebra K R] :
    Multiplicative (Module.End K V ⊗[K] R) ≃*
      Multiplicative (Module.End R (R ⊗[K] V)) :=
  (endVectorLinearEquiv K V R).toAddEquiv.toMultiplicative

end End
end AlgebraicGeometry
end
end
