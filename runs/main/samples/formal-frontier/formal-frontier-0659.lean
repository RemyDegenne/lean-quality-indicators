set_option warningAsError true

@[expose] public section

open CategoryTheory TopologicalSpace

namespace RingedSpaces.Modules.RingedSpacePullback

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

theorem triangle_identities
    (M : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf Y))
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)) :
    (pullbackFunctor f).map ((adjunction f).unit.app M) ≫
        (adjunction f).counit.app ((pullbackFunctor f).obj M) = 𝟙 _ ∧
      (adjunction f).unit.app ((RingedSpacePushforward.pushforwardFunctor f).obj N) ≫
        (RingedSpacePushforward.pushforwardFunctor f).map ((adjunction f).counit.app N) =
          𝟙 _ :=
  ⟨(adjunction f).left_triangle_components M, (adjunction f).right_triangle_components N⟩

end RingedSpaces.Modules.RingedSpacePullback
end
