@[expose] public section

open CategoryTheory Function

namespace Profinite.FinitePresentation

universe u

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

/-- Project a common finite-stage index to its target quotient. -/
def surjectiveTargetIndex : SurjectiveIndex f ⥤ DiscreteQuotient Y :=
  (show Monotone (fun P : SurjectiveIndex f ↦ P.1.2) from fun _ _ h ↦ h.2).functor

end Profinite.FinitePresentation
end
