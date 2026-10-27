@[expose] public section

namespace Submodule

open TensorProduct

variable {R M : Type*} (A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] (p q : Submodule R M)

/-- If `A` is an `R`-algebra, any `R`-submodule `p` of an `R`-module `M` may be pushed forward to
an `A`-submodule of `A ⊗ M`.

This "base change" operation is also known as "extension of scalars". -/
def baseChange : Submodule A (A ⊗[R] M) :=
  LinearMap.range (p.subtype.baseChange A)

end Submodule
end
