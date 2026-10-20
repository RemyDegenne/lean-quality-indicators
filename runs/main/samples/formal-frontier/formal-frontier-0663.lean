@[expose] public section

set_option warningAsError true

set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) [IsIntegral Y]

theorem genericPointRationalHom_boundary {S : Scheme.{u}} (sY : Y ⟶ S)
    [JacobsonSpace Y] [Nontrivial Y] :
    IsIso (genericPointRationalHom Y sY).toRationalMap.functionFieldMap ∧
      ¬ IsIso (genericPointRationalHom Y sY) := by
  constructor
  · simpa only [genericPointRationalHom_toRationalMap,
      IntegralDominantRationalSchemeOver.of] using
      (inferInstance : IsIso
        (Y.fromSpecStalk (genericPoint Y)).toRationalMap.functionFieldMap)
  · intro hIso
    let forward := genericPointRationalHom Y sY
    haveI : IsIso forward := hIso
    haveI hsource : Subsingleton
        (IntegralDominantRationalSchemeOver.of
          (Y.fromSpecStalk (genericPoint Y) ≫ sY)).toScheme := by
      change Subsingleton (PrimeSpectrum Y.functionField)
      infer_instance
    haveI : JacobsonSpace (IntegralDominantRationalSchemeOver.of sY).toScheme := by
      change JacobsonSpace Y
      infer_instance
    haveI : Nontrivial (IntegralDominantRationalSchemeOver.of sY).toScheme := by
      change Nontrivial Y
      infer_instance
    have hforward : forward.toRationalMap.comp (inv forward).toRationalMap =
        RationalMap.id (Spec Y.functionField) := by
      have h := congrArg (fun arrow => arrow.toRationalMap) (IsIso.hom_inv_id forward)
      rw [IntegralDominantRationalSchemeOver.toRationalMap_comp,
        IntegralDominantRationalSchemeOver.toRationalMap_id] at h
      simpa only [IntegralDominantRationalSchemeOver.of] using h
    have hreverse : (inv forward).toRationalMap.comp forward.toRationalMap =
        RationalMap.id Y := by
      have h := congrArg (fun arrow => arrow.toRationalMap) (IsIso.inv_hom_id forward)
      rw [IntegralDominantRationalSchemeOver.toRationalMap_comp,
        IntegralDominantRationalSchemeOver.toRationalMap_id] at h
      simpa only [IntegralDominantRationalSchemeOver.of] using h
    exact RationalMap.not_twoSidedInverse_of_subsingleton_of_jacobson
      forward.toRationalMap (inv forward).toRationalMap ⟨hforward, hreverse⟩

end AlgebraicGeometry.Scheme
end
end
