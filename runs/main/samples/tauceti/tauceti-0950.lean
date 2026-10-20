public section

noncomputable section

open Bornology Complex Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

theorem schwarzChristoffelPolygon_boundary_subset_halfSpace
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    (schwarzChristoffelPolygon a e z₀).boundary ℝ ⊆
      {z | (schwarzChristoffelVertex a e z₀ 0).im ≤ z.im} := by
  rw [schwarzChristoffelPolygon_boundary]
  rintro z ((hz | hz) | hz)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (convex_halfSpace_im_ge _).segment_subset
      (im_schwarzChristoffelVertex_zero_le a e z₀ ha he hsum i.castSucc)
      (im_schwarzChristoffelVertex_zero_le a e z₀ ha he hsum i.succ) hi
  · exact (convex_halfSpace_im_ge _).segment_subset
      (im_schwarzChristoffelVertex_zero_le a e z₀ ha he hsum (Fin.last n))
      (im_schwarzChristoffelVertexAtInfinity_eq_im_zero a e z₀ ha he hsum).ge hz
  · have hinfty :=
      (im_schwarzChristoffelVertexAtInfinity_eq_im_zero a e z₀ ha he hsum).ge
    have hzero : (schwarzChristoffelVertex a e z₀ 0).im ≤
      (schwarzChristoffelVertex a e z₀ 0).im := le_rfl
    exact (convex_halfSpace_im_ge _).segment_subset hinfty hzero hz

end TauCeti
end
end
