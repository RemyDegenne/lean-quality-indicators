public section

set_option warningAsError true

open CategoryTheory Opposite TopologicalSpace

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}

/-- The inclusion of the nilradical module into the structure sheaf. -/
noncomputable def nilradicalModuleι (X : Scheme.{u}) :
    X.nilradicalModule ⟶ SheafOfModules.unit X.ringCatSheaf :=
  X.nilradical.toModuleι

end AlgebraicGeometry.Scheme
end
