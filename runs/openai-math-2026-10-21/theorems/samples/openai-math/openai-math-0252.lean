namespace OAI

open Set MeasureTheory

namespace CylinderCovering.Footprints

theorem absoluteFootprint_piece_interiors_nonempty {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 < B) :
    (interior (affineFootprint m (M + A * d) d 0 B)).Nonempty ∧
      (interior (radialReflection '' affineFootprint (-m) (A * d) d 0 B)).Nonempty := by
  have hAd : 0 < A * d := mul_pos hA hd
  constructor
  · exact affineFootprint_interior_nonempty (add_nonneg hM hAd.le) hd le_rfl
      (by simpa using hB) (by simpa using add_pos_of_nonneg_of_pos hM hAd)
  · have hneg := affineFootprint_interior_nonempty (m := -m) hAd.le hd le_rfl
      (by simpa using hB) (by simpa using hAd)
    have hsurj : Function.Surjective radialReflection :=
      fun p => ⟨radialReflection p, radialReflection_involutive p⟩
    have hopen : IsOpenMap radialReflection :=
      radialReflection.toAffineMap.isOpenMap
        (by change Continuous (fun p : ℝ × ℝ => (-p.1, p.2)); fun_prop) hsurj
    exact (hneg.image radialReflection).mono (hopen.image_interior_subset _)

end CylinderCovering.Footprints
end OAI
