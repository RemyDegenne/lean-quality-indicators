public section

open CategoryTheory Category Limits

namespace TauCeti

universe u v v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

@[simp]
theorem sheafificationIso_hom (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{v} R) :
    (sheafificationIso R M).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M := by
  simp only [sheafificationIso]
  rfl

end SheafOfModules
end
end TauCeti
end
