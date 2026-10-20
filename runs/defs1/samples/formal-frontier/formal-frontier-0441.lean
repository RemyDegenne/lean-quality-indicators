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

/-- A topological open site discharges every sheaf-level hypothesis at matched universes. -/
noncomputable def opensTensorSheafAdjunction {X : TopCat.{u}}
    (A B : TopCat.Sheaf CommRingCat.{u} X) (theta : A ⟶ B) :
    tensorSheafFunctor A B theta ⊣
      SheafOfModules.restrictScalars (ringSheafMap A B theta) := by
  let : HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    opensWeakSheafify X
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    opensWEqualsLocallyBijective X
  exact tensorSheafAdjunction A B theta

end RingedSpaces.Modules
end
