@[expose] public section

variable {M N P σ : Type*}

namespace MulHom

open Subsemigroup

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

/-- The range of a semigroup homomorphism is a subsemigroup. See Note [range copy pattern]. -/
@[to_additive /-- The range of an `AddHom` is an `AddSubsemigroup`. -/]
def srange (f : M →ₙ* N) : Subsemigroup N :=
  ((⊤ : Subsemigroup M).map f).copy (Set.range f) Set.image_univ.symm

end MulHom
end
