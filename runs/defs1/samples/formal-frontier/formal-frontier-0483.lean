@[expose] public section

open CategoryTheory

open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry

universe u v

namespace FiniteGroupFunctions

variable {K : Type u} {Γ : Type v} {R S : Type*}

variable [CommRing K] [Fintype Γ]

namespace Points

/-- Implementation type for finite clopen/idempotent partitions. -/
abbrev IdempotentPartitions (Γ R : Type*) [Fintype Γ] [CommRing R] :=
  {e : Γ → R // CompleteOrthogonalIdempotents e}

end Points
end FiniteGroupFunctions
end AlgebraicGeometry
end
