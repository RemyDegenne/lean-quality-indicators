public section

set_option warningAsError true

open CategoryTheory Opposite TopologicalSpace

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}

namespace IdealSheafData

/-- The canonical inclusion of an ideal sheaf module into the structure sheaf. -/
@[expose]
noncomputable def toModuleι (I : X.IdealSheafData) :
    I.toModule ⟶ SheafOfModules.unit X.ringCatSheaf :=
  I.toSubmodule.ι

end IdealSheafData
end AlgebraicGeometry.Scheme
end
