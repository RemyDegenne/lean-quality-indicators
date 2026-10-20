public section

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.CommRingForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)

theorem canonicalComponent_mate (A : Y.Sheaf CommRingCat.{v}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _
      (canonicalComponent g A) =
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A) := by
  exact Equiv.apply_symm_apply _ _

end TopCat.Sheaf.CommRingForget
end
