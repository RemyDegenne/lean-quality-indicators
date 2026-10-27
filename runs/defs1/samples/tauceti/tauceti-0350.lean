public section

open CategoryTheory

open TauCeti.SheafOfModules (ringCatSheaf)

universe u v₁ v₂ u₁ u₂

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (R : Sheaf J CommRingCat.{u})

namespace SheafOfModules

variable {R}

section Pushforward

open TauCeti.SheafOfModules (pushforwardCommRing pushforwardModule pushforwardRingIso
  pushforwardSheafificationIso pushforwardSheafificationNatIso
  pushforwardSheafificationNatIso_hom_app)

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : D ⥤ C) [F.IsContinuous K J] [F.IsCocontinuous K J]

/-- The restriction of a symmetric power to a slice site is the symmetric power of the
restriction. -/
def overSymmetricPowerIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ((symmetricPower R n).obj M).over X ≅ (symmetricPower (R.over X) n).obj (M.over X) :=
  pushforwardSymmetricPowerIso (K := J.over X) (Over.forget X) n M

end Pushforward
end SheafOfModules
end
end
