public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory Opposite

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

variable (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)

@[reassoc (attr := simp)]
theorem toSheafify_comp_fppfHomogeneousQuotientSheafProjection :
    toSheafify (CommAlgCat.fppfTopology R) (pointsPresheafGrp H).X ≫
        eqToHom (congrArg
          (fun X : Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)) ↦ X.obj)
          (pointsFppfGroupObject_X_eq H).symm) ≫
          (fppfHomogeneousQuotientSheafProjection H I).hom =
      eqToHom ((pointsPresheafGrp_X_eq H).trans
        (pointsGroupPresheaf_ulift_forget_eq_pointsPresheaf_ulift H)) ≫
          fppfHomogeneousQuotientProjection H I := by
  rw [fppfHomogeneousQuotientProjection_def]
  simp [fppfHomogeneousQuotientSheafProjection, Category.assoc,
    sheafifyMap, ObjectProperty.eqToHom_hom]

end CommHopfAlgCat
end
