@[expose] public section

open CategoryTheory TopologicalSpace

universe u

attribute [instance] FiniteDiscretePresentation.smallCategory
  FiniteDiscretePresentation.cofiltered

namespace FiniteDiscretePresentation

variable {X : Type u} [TopologicalSpace X] (P : FiniteDiscretePresentation X)

/-- The presentation diagram, viewed as a diagram of topological spaces. -/
abbrev topDiagram : P.index ⥤ TopCat.{u} :=
  letI : SmallCategory P.index := P.smallCategory
  ((P.diagram ⋙ FintypeCat.toProfinite) ⋙ profiniteToCompHaus) ⋙ compHausToTop

end FiniteDiscretePresentation
end
