public section

open scoped TensorProduct

universe u v w

namespace Subalgebra

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [Algebra K R]

/-- A subalgebra is finite etale when its induced algebra structure is finite
and etale. -/
abbrev IsFiniteEtale (A : Subalgebra K R) : Prop :=
  Algebra.IsFiniteEtale K A

end Subalgebra
end
