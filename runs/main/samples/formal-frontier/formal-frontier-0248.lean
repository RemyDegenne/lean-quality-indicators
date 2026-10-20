public section

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.AbelianForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)

theorem canonicalComponent_isIso (A : Y.Sheaf AddCommGrpCat.{v}) :
    IsIso (canonicalComponent g A) := by
  rw [canonicalComponent_eq_construction]
  infer_instance

end TopCat.Sheaf.AbelianForget
end
