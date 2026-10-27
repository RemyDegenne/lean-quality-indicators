@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v v' v'' u u' u''

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u} [Category.{v} C]

variable {F : J ⥤ C}

section Opposite

/-- `t : Cone F` is a limit cone if and only if `t.op : Cocone F.op` is a colimit cocone. -/
@[to_dual
/-- `t : Cocone F` is a colimit cocone if and only if `t.op : Cone F.op` is a limit cone. -/]
def isLimitEquivIsColimitOp {t : Cone F} : IsLimit t ≃ IsColimit t.op :=
  equivOfSubsingletonOfSubsingleton IsLimit.op isLimitOfOp

end Opposite
end CategoryTheory.Limits
end
end
