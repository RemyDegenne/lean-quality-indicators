set_option warningAsError true

@[expose] public section

open CategoryTheory TopologicalSpace

namespace RingedSpaces.Modules.RingedSpacePullback

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The explicit right-tensor, sheafified pullback.
Vakil's *The Rising Sea* (21 October 2025 draft), Exercise 7.2.D(b)
(p. 205), requests full-morphism pullback; the project construction
sheafifies a genuine right-factor tensor after inverse image. -/
noncomputable def pullbackFunctor :
    SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y) ⥤
      SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X) := by
  letI := opensWeakSheafify X.carrier
  letI := opensWEqualsLocallyBijective X.carrier
  exact SheafInverseImage.moduleFunctor f.hom.base Y.sheaf ⋙
    rightSheafFunctor (inverseRing f) X.sheaf (coefficientMap f)

end RingedSpaces.Modules.RingedSpacePullback
end
