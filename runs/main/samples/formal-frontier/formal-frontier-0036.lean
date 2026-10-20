public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompactRep

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

@[simp] theorem compactUniversalNormQuotientMap_id
    (A : LevelCompactRep.{u, u, u} R G) :
    compactUniversalNormQuotientMap (𝟙 A) = 𝟙 _ := by
  apply CompHausAddCommGrp.hom_ext
  ext x
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    change compactUniversalNormQuotientMap (𝟙 A) (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk x
    rw [compactUniversalNormQuotientMap_mk, groupMap_id]
    rfl

end ContinuousGroupCohomology.LevelCompactRep
end
end
