@[expose] public noncomputable section

universe w' w'' w₀ w₁ v'' v' v u

namespace Module

variable (A : Type u) [Ring A]

variable (M : Type v) [AddCommGroup M] [Module A M]

variable {A M}

/-- Constructor for `Module.Presentation`. -/
@[simps toRelations toSolution]
def Presentation.ofIsPresentation {relations : Relations.{w₀, w₁} A}
    {solution : relations.Solution M} (h : solution.IsPresentation) :
    Presentation.{w₀, w₁} A M where
  __ := relations
  toSolution := solution
  toIsPresentation := h

end Module
end
