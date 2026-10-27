@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [Ring R]

namespace FiniteProjective

section Isomorphisms

variable {R} {X Y : FiniteProjective.{u, v} R}

/-- A linear equivalence of finite projective modules gives a categorical
isomorphism. -/
def isoOfLinearEquiv (e : X ≃ₗ[R] Y) : X ≅ Y :=
  (isFiniteProjective R).isoMk e.toModuleIso

end Isomorphisms
end FiniteProjective
end ModuleCat
end
