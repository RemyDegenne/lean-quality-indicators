public section

set_option warningAsError true

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The affine `fromTildeΓ` condition gives a presentation of the original
restriction to the affine open, before transport to the over-site. -/
noncomputable def presentationRestrictAffineOpenOfIsIsoFromTildeΓ
    (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    [hFrom : IsIso (((M.restrict U.ι).restrict hU.isoSpec.inv).fromTildeΓ)] :
    (M.restrict U.ι).Presentation := by
  let Mᵤ := M.restrict U.ι
  let N := Mᵤ.restrict hU.isoSpec.inv
  let hN : IsIso N.fromTildeΓ := by
    simpa [N, Mᵤ] using hFrom
  let P := presentationRestrict hU.isoSpec.hom
    (@presentationOfIsIsoFromTildeΓ _ N hN)
  let α :=
    ((restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).app Mᵤ).symm ≪≫
      (restrictFunctorCongr hU.isoSpec.hom_inv_id).app Mᵤ ≪≫
      restrictFunctorId.app Mᵤ
  exact @SheafOfModules.Presentation.ofIsIso
    _ _ _ _ _ _ _ _ α.hom α.isIso_hom P

end AlgebraicGeometry.Scheme.Modules
end
