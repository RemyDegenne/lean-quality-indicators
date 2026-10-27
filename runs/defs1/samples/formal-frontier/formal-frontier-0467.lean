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

/-- The explicit sheaf extension-of-scalars functor. -/
noncomputable def tensorSheafFunctor (theta : A ⟶ B) : Sheaves A ⥤ Sheaves B :=
  (SheafOfModules.forget (ringSheaf A)) ⋙
    tensorPresheafFunctor A.obj B.obj theta.hom ⋙ moduleSheafification B

end RingedSpaces.Modules
end
