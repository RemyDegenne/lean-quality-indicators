public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.IsFrobenius

variable {E : ExactStructure C} (hE : E.IsFrobenius)

theorem isProjective_suspensionObj {X : C} (hX : E.isProjective X) :
    E.isProjective (hE.suspensionObj X) := by
  let s := E.splittingOfInjective (hE.suspensionPresentation X).conflation
    ((hE.projective_iff_injective X).mp hX)
  exact E.isProjective.prop_of_retract
    ⟨s.s, hE.suspensionDeflation X, s.s_g⟩
    ((hE.projective_iff_injective _).mpr
      (hE.suspensionPresentation X).isInjective)

end ExactStructure.IsFrobenius
end TauCeti
end
