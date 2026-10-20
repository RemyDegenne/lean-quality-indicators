@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [Ring R]

namespace FiniteProjective

section Representatives

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

@[simp]
theorem repr_carrier : (repr R P : Type u) = Module.Finite.repr R P := rfl

end Representatives
end FiniteProjective
end ModuleCat
end
