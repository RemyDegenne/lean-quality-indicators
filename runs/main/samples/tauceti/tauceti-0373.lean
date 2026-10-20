public section

open CategoryTheory MonoidalCategory ExactPairing Functor.LaxMonoidal Functor.OplaxMonoidal

universe v u

namespace TauCeti

attribute [instance] PivotalCategory.pivotalIso_isMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

open PivotalCategory

theorem pivotalIsoApp_unit_inv :
    (pivotalIsoApp (𝟙_ C)).inv = η (doubleRightDualFunctor C) :=
  Iso.inv_ext ((congrArg (· ≫ η (doubleRightDualFunctor C)) pivotalIsoApp_unit_hom).trans
    (Functor.Monoidal.ε_η _))

end TauCeti
end
