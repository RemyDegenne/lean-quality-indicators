@[expose] public section

noncomputable section

universe w' w v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Under

/-- If `c` is a limit cone, then so is the cone `c.toUnder` with cone point `𝟙 c.pt`. -/
def isLimitToUnder {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) : IsLimit c.toUnder :=
  isLimitOfReflects (forget c.pt) (IsLimit.equivIsoLimit c.mapConeToUnder.symm hc)

end CategoryTheory.Under
end
end
