public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.RestrictedLevelCompactRep

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

local instance : Nonempty (OpenNormalSubgroup G) :=
  ⟨⟨⊤, by change (⊤ : Subgroup G).Normal; infer_instance⟩⟩

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

@[reassoc] theorem restrictedNormLimitIso_inv_π
    (B : RestrictedLevelCompactRep R G) (U : OpenNormalSubgroup G) :
    (restrictedNormLimitIso B).inv ≫ limit.π (restrictedNormDiagram B) U ≫
        groupMap (fullInclusion B) U =
      limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U := by
  have hcomm := congrArg
    (fun m : limit (restrictedNormDiagram B) ⟶
        (restrictedNormDiagram (full B.toLevelCompactRep)).obj U =>
      (restrictedNormLimitIso B).inv ≫ m)
        (restrictedNormLimitIso_hom_π B U)
  have hcancel : (restrictedNormLimitIso B).inv ≫
      ((restrictedNormLimitIso B).hom ≫
        limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U) =
          limit.π (restrictedNormDiagram (full B.toLevelCompactRep)) U := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact hcomm.symm.trans hcancel

end ContinuousGroupCohomology.RestrictedLevelCompactRep
end
end
