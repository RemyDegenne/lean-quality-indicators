@[expose] public section

noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The same pairwise diagram, regarded as a diagram in the category of categories. -/
def openCoverCatDiagram (U : ι → Opens X) : Pairwise ι ⥤ Cat.{u, u} :=
  openCoverDiagram U ⋙ Grpd.forgetToCat

end FundamentalGroupoid
end
end
