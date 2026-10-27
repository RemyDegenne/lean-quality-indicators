@[expose] public section

noncomputable section Ring

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]

variable {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]

variable (p q : Submodule R E)

variable {S : Type*} [Semiring S] {M : Type*} [AddCommMonoid M] [Module S M] (m : Submodule S M)

namespace Submodule

open LinearMap

/-- Projection to a submodule along a complement. It is the unique
linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.

For the projection from `E` to `E`, see `Submodule.projection`. See also:
* `Submodule.projectionOntoL` and `Submodule.projectionL` for the continuous versions.
* `Submodule.orthogonalProjection` and `Submodule.orthogonalProjectionOnto` for the projections
  along the orthogonal subspace.

See also `LinearMap.linearProjOfIsCompl`. -/
def projectionOnto (h : IsCompl p q) : E →ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm

end Submodule
end Ring
end
