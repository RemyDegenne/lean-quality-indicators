@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable (K : Type u) (Γ : Type v)

/-- Forget the dedicated Hopf-algebra type and view its elements as ordinary functions. -/
def toPiAlgEquiv [CommRing K] : FiniteGroupFunctions K Γ ≃ₐ[K] (Γ → K) :=
  AlgEquiv.refl

end FiniteGroupFunctions
end AlgebraicGeometry
end
