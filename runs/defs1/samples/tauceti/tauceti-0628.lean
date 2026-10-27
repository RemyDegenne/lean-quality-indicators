public section

namespace TauCeti

open CategoryTheory

open scoped ModuleCat

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

section ExactStructure

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]

open CategoryTheory.Limits CategoryTheory.ObjectProperty

open scoped ZeroObject

/-- The exact structure on pointwise finite-dimensional quiver representations. -/
noncomputable def pointwiseFiniteDimensionalQuiverRepresentationsExactStructure :
    ExactStructure (ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q)) :=
  (ExactStructure.abelian _).fullSubcategory _
    (isExtensionClosed_pointwiseFiniteDimensionalQuiverRepresentations k Q)

end ExactStructure
end TauCeti
end
