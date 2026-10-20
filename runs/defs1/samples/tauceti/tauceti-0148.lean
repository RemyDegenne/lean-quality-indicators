public section

open CategoryTheory MonoidalCategory

open TauCeti.SheafOfModules (ringCatSheaf)

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {R : Sheaf J CommRingCat.{u}}

namespace SheafOfModules

/-- The multiplication `Symⁱ M ⊗ Symʲ M ⟶ Symⁱ⁺ʲ M` of symmetric powers of a sheaf of modules:
the sheafification of the sectionwise multiplication of symmetric powers, preceded by the tensor
comparison of sheafification. -/
def symmetricPowerMul (M : SheafOfModules.{u} (ringCatSheaf R)) (i j : ℕ) :
    (symmetricPower R i).obj M ⊗ (symmetricPower R j).obj M ⟶ (symmetricPower R (i + j)).obj M :=
  ((symmetricPowerIso i M).hom ⊗ₘ (symmetricPowerIso j M).hom) ≫
    Functor.LaxMonoidal.μ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)) _ _ ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        (PresheafOfModulesOfCommRing.symmetricPowerMul M.val i j) ≫
      (symmetricPowerIso (i + j) M).inv

end SheafOfModules
end
end
