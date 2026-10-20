public section

set_option warningAsError true

open CategoryTheory TopologicalSpace

open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

theorem isCoherentQuasicoherent_iff_affineOpenCover
    (X : Scheme.{u})
    (Q : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i)) :
    let M : X.Modules := Q.obj
    let _ : M.IsQuasicoherent := Q.property
    isCoherentQuasicoherent X Q ↔
      ∀ i, isCoherentOnSpec Γ(X, U i)
        (⟨(M.restrict (U i).ι).restrict (hUaff i).isoSpec.inv,
          by infer_instance⟩ :
          (SheafOfModules.isQuasicoherent
            (Spec Γ(X, U i)).ringCatSheaf).FullSubcategory) := by
  let M : X.Modules := Q.obj
  let _ : M.IsQuasicoherent := Q.property
  change (∀ V : X.affineOpens,
      isCoherentOnSpec Γ(X, (V : X.Opens))
        (⟨(M.restrict V.1.ι).restrict V.2.isoSpec.inv,
          by infer_instance⟩ :
          (SheafOfModules.isQuasicoherent
            (Spec Γ(X, (V : X.Opens))).ringCatSheaf).FullSubcategory)) ↔
    ∀ i, isCoherentOnSpec Γ(X, U i)
      (⟨(M.restrict (U i).ι).restrict (hUaff i).isoSpec.inv,
        by infer_instance⟩ :
        (SheafOfModules.isQuasicoherent
          (Spec Γ(X, U i)).ringCatSheaf).FullSubcategory)
  constructor
  · intro h i
    exact h ⟨U i, hUaff i⟩
  · intro h V
    rw [isCoherentOnSpec_restrict_affineOpen_iff M V.1 V.2]
    apply of_affine_open_cover
      (P := fun W ↦ Module.IsCoherent Γ(X, (W : X.Opens)) Γ(M, (W : X.Opens)))
      (fun i ↦ ⟨U i, hUaff i⟩) hU.iSup_eq_top V
    · intro W f hW
      exact isCoherent_basicOpen_of_qcqs M W.2.isCompact
        W.2.isQuasiSeparated f hW
    · intro W s hs hWs
      exact isCoherent_of_span_basicOpen_of_qcqs M W.2.isCompact
        W.2.isQuasiSeparated (s : Set Γ(X, (W : X.Opens))) hs hWs
    · intro i
      exact (isCoherentOnSpec_restrict_affineOpen_iff
        M (U i) (hUaff i)).mp (h i)

end AlgebraicGeometry.Scheme.Modules
end
