namespace OAI

open Set MeasureTheory

open RuledApproximation

open scoped InnerProductSpace

noncomputable section

namespace CylinderCovering.AngularGeneral

lemma ambient_area_of_intrinsic (C : Cylinder) :
    TriangularCovering.area ((Subtype.val :
      ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ) → Space) '' C.base) = C.area := by
  unfold TriangularCovering.area Cylinder.area
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image]
  have hm : (Measure.euclideanHausdorffMeasure 2 :
      Measure ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ)) = volume := by
    simpa only [perpendicularPlane_finrank _ C.unit_axis] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
        (V := ((Submodule.span ℝ ({C.axis} : Set Space))ᗮ)))
  rw [hm]
  rfl

end CylinderCovering.AngularGeneral
end
end OAI
