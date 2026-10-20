public section

open scoped DirectSum

namespace SymmetricAlgebra

universe u v

variable {R : Type u} {M : Type v}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The degree-`n` part of a symmetric algebra: the `n`-th power of the submodule spanned by
its canonical generators. -/
abbrev homogeneousSubmodule (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  LinearMap.range (SymmetricAlgebra.ι R M) ^ n

end SymmetricAlgebra
end
