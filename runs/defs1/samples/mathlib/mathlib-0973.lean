@[expose] public section

noncomputable section

universe w' w v u

open CategoryTheory CategoryTheory.Limits

variable {J : Type w} [Category.{w'} J]

variable {C : Type u} [Category.{v} C]

variable {X : C}

namespace CategoryTheory.Under

/-- If `F` has a limit, then the cone `limit.toUnder F` with cone point `𝟙 (limit F)` is
    also a limit cone. -/
def _root_.CategoryTheory.Limits.limit.isLimitToOver (F : J ⥤ C) [HasLimit F] :
    IsLimit (limit.toUnder F) :=
  Under.isLimitToUnder (limit.isLimit F)

end CategoryTheory.Under
end
end
