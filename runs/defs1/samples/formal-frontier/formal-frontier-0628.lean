public section

set_option warningAsError true

open CategoryTheory Opposite TopologicalSpace

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}

namespace IdealSheafData

/-- An ideal sheaf as a subobject of the structure sheaf. -/
@[expose]
noncomputable def toModuleSubobject (I : X.IdealSheafData) :
    @Subobject X.Modules (inferInstance : Category X.Modules)
      (SheafOfModules.unit X.ringCatSheaf) := by
  letI : Mono I.toModuleι := toModuleι_mono I
  exact Subobject.mk I.toModuleι

end IdealSheafData
end AlgebraicGeometry.Scheme
end
