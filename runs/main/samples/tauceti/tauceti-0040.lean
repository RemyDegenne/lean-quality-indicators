public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

@[simp]
lemma freePUnitIsoUnit_inv (S : Sheaf J RingCat.{u}) :
    (freePUnitIsoUnit S).inv =
      _root_.SheafOfModules.ιFree (R := S) PUnit.unit := by
  exact coproductUniqueIso_inv (fun _ : PUnit.{u + 1} ↦
    _root_.SheafOfModules.unit.{v₁, u₁, u} S)

end SheafOfModules
end
end TauCeti
end
