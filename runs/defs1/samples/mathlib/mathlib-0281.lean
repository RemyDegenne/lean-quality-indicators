@[expose] public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

universe w' w₂' w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {J : Type w} [Category.{w'} J] {K : J ⥤ C}

attribute [instance 100]
  PreservesLimitsOfShape.preservesLimit PreservesLimitsOfSize.preservesLimitsOfShape
  PreservesColimitsOfShape.preservesColimit
  PreservesColimitsOfSize.preservesColimitsOfShape

/-- A convenience function for `PreservesLimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def isLimitOfPreserves (F : C ⥤ D) {c : Cone K} (t : IsLimit c) [PreservesLimit K F] :
    IsLimit (F.mapCone c) :=
  (PreservesLimit.preserves t).some

end CategoryTheory.Limits
end
end
