public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed PresheafOfModules

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

variable {R}

@[simp]
theorem _root_.SheafOfModules.dualIso_hom
    {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)} (e : M ≅ N) :
    (_root_.SheafOfModules.dualIso e).hom =
      (pre e.inv).app (_root_.SheafOfModules.unit (ringCatSheaf R)) := by
  simp only [_root_.SheafOfModules.dualIso, asIso_hom]

end SheafOfModules
end
end TauCeti
end
