public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (X : Cᵒᵖ)

@[simp]
lemma evaluation_ε : ε (evaluation (R := R) X) = 𝟙 _ :=
  rfl

end PresheafOfModulesOfCommRing
end
end TauCeti
end
