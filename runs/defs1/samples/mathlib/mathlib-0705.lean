@[expose] public section

universe w

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

namespace TopCat

variable {C : Type*} [Category* C]

variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type*} (U : ι → Opens X)

namespace Presheaf

namespace SheafCondition

/-- The category of open sets contained in some element of the cover.
-/
def OpensLeCover : Type w :=
  ObjectProperty.FullSubcategory fun V : Opens X ↦ ∃ i, V ≤ U i

end SheafCondition
end Presheaf
end TopCat
end
end
