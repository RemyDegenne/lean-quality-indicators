public section

namespace TauCeti

open scoped TensorProduct

section Defs

variable {K L A : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
  [Semiring A] [Algebra K A]

/-- `A` regarded as a module over the scalar extension `L ⊗[K] A`, along a `K`-algebra homomorphism
`f : L →ₐ[K] A` out of a **commutative** algebra: the pure tensor `l ⊗ₜ a` acts by
`x ↦ a * x * f l`.

Equivalently this is the `A`-`L`-bimodule `A`, with `A` acting on the left by multiplication and
`L` on the right through `f`; commutativity of `L` is what lets the right action be packaged as a
left action of `L ⊗[K] A` with no opposite algebra. It is a type synonym for `A` so that `A` itself
is left without an `L ⊗[K] A`-action, and so that different subfields can act at the same time. -/
@[expose] def BaseChangeModule (f : L →ₐ[K] A) : Type _ :=
  Bimodule (f.toOppositeOfComm)

end Defs
end TauCeti
end
