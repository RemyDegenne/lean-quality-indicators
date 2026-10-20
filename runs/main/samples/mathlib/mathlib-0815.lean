@[expose] public noncomputable section

open Module

section StrictOrderedCommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

namespace SameRay

variable {x y z : M}

@[nontriviality]
theorem of_subsingleton' [Subsingleton R] (x y : M) : SameRay R x y :=
  haveI := Module.subsingleton R M
  of_subsingleton x y

end SameRay
end StrictOrderedCommSemiring
end
