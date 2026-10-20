set_option warningAsError true

@[expose] public section

open CategoryTheory TopologicalSpace

namespace RingedSpaces.Modules.RingedSpacePullback

universe u

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)

theorem nativeComparison_counit
    (N : SheafOfModules.{u} (RingedSpacePushforward.ringSheaf X)) :
    (nativeComparison f).hom.app ((RingedSpacePushforward.pushforwardFunctor f).obj N) ≫
      (nativeAdjunction f).counit.app N = (adjunction f).counit.app N :=
  Adjunction.leftAdjointUniq_hom_app_counit (adjunction f) (nativeAdjunction f) N

end RingedSpaces.Modules.RingedSpacePullback
end
