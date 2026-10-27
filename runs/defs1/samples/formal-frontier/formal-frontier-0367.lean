public section

open scoped TensorProduct

namespace GaloisDescent

universe u v w

variable {k : Type u} {L : Type v} {R : Type w}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [CommRing R] [Algebra k R]

/-- The honest preimage in the original algebra of a scalar-extended subalgebra. -/
def descended (P : Subalgebra L (L ⊗[k] R)) : Subalgebra k R :=
  (P.restrictScalars k).comap Algebra.TensorProduct.includeRight

end GaloisDescent
end
