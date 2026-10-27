@[expose] public section

open CategoryTheory TopologicalSpace

open scoped ChangeOfRings

universe u v₁ u₁

namespace RingedSpaces.Modules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})

variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The native adjunction governing module sheafification. -/
noncomputable def moduleSheafificationAdjunction :
    moduleSheafification B ⊣
      SheafOfModules.forget (ringSheaf B) ⋙
        PresheafOfModules.restrictScalars (𝟙 (ringSheaf B).obj) := by
  change PresheafOfModules.sheafification (𝟙 (ringSheaf B).obj) ⊣ _
  exact PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf B).obj)

end RingedSpaces.Modules
end
