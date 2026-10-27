public section

open scoped TensorProduct

namespace SeparableClosureDescent

universe u v w x y

section Package

variable {k : Type u} {K : Type w} {R : Type x}
  [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
  [CommRing R] [Algebra k R]

/-- The complete literal output of separable-closure descent. -/
structure Package (P : Subalgebra K (K ⊗[k] R)) where
  /-- The reconstructed algebra in the original ambient algebra. -/
  algebra : Subalgebra k R
  /-- The reconstructed subalgebra is finite etale over `k`. -/
  isFiniteEtale : algebra.IsFiniteEtale
  /-- Canonical orientation from scalar extension to the given subalgebra. -/
  reconstruction : K ⊗[k] algebra ≃ₐ[K] P
  /-- Reconstruction is the literal ambient scalar-extension inclusion. -/
  coe_reconstruction (z : K ⊗[k] algebra) :
    ((reconstruction z : P) : K ⊗[k] R) = scalarExtensionMap algebra z
  /-- The descended algebra is the honest preimage in `R`. -/
  mem_algebra (r : R) :
    r ∈ algebra ↔ (Algebra.TensorProduct.includeRight r : K ⊗[k] R) ∈ P

end Package
end SeparableClosureDescent
end
