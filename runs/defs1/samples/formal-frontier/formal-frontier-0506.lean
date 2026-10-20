@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [instance] FiniteDiscretePresentation.smallCategory
  FiniteDiscretePresentation.cofiltered

namespace FiniteDiscretePresentation

variable {X : Type u} [TopologicalSpace X] (P : FiniteDiscretePresentation X)

/-- The composite of the presentation homeomorphism with a limit projection. -/
def stage (j : P.index) : X → P.stageSpace j :=
  P.stageMap j

end FiniteDiscretePresentation
end
