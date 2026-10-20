@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [Ring R]

namespace FiniteProjective

section IsomorphismClasses

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

@[simp]
theorem isoClass_ulift : isoClass R (ULift.{w} P) = isoClass R P :=
  toSkeleton_repr_ulift R P

end IsomorphismClasses
end FiniteProjective
end ModuleCat
end
