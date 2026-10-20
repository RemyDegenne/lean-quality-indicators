@[expose] public section

universe uR uM

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable (R : Type uR) [Ring R]

/-- The property of a module being both finitely generated and projective. -/
def isFiniteProjective : ObjectProperty (ModuleCat.{uM} R) :=
  fun P ↦ Module.Finite R P ∧ Module.Projective R P

end ModuleCat
end
