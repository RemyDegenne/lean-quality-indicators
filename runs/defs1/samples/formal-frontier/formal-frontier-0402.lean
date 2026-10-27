@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [instance] FiniteDiscretePresentation.smallCategory
  FiniteDiscretePresentation.cofiltered

namespace FiniteDiscretePresentation

variable {X : Type u} [TopologicalSpace X] (P : FiniteDiscretePresentation X)

/-- The canonical presentation using all discrete quotients of a profinite space. -/
noncomputable def ofProfinite (X : Profinite.{u}) :
    FiniteDiscretePresentation X where
  index := DiscreteQuotient X
  diagram := X.fintypeDiagram
  equiv := CompHausLike.homeoOfIso X.isoAsLimitConeLift

end FiniteDiscretePresentation
end
