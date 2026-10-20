public section

set_option warningAsError true

open CategoryTheory TopologicalSpace

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

lemma isCoherentOnSpec_restrict_affineOpen_iff
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (V : X.Opens) (hV : IsAffineOpen V) :
    isCoherentOnSpec Γ(X, V)
      (⟨(M.restrict V.ι).restrict hV.isoSpec.inv,
        by infer_instance⟩ :
        (SheafOfModules.isQuasicoherent
          (Spec Γ(X, V)).ringCatSheaf).FullSubcategory) ↔
      Module.IsCoherent Γ(X, V) Γ(M, V) := by
  rw [isCoherentOnSpec_iff]
  exact Module.IsCoherent.equiv_iff (affineOpenSectionsLinearEquiv M V hV)

end AlgebraicGeometry.Scheme.Modules
end
