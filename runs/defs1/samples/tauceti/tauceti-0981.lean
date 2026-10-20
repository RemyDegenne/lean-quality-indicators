public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The cohomology of the trivial line bundle is base-linearly equivalent to that of the structure
sheaf. -/
def _root_.AlgebraicGeometry.Scheme.Modules.trivialCohomologyBaseLinearEquiv (i : ℕ) :
    let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
    Cohomology (InvertibleSheaf.trivial X).obj i ≃ₗ[R]
      Cohomology M i := by
  let M : X.Modules := SheafOfModules.unit X.ringCatSheaf
  exact
    cohomologyBaseLinearEquivOfIso R (M := (InvertibleSheaf.trivial X).obj)
      (N := M)
      (InvertibleSheaf.trivialObjIsoUnit X) i

end TauCeti.AlgebraicGeometry
end
end
