public section

open Set Filter Topology

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

theorem dr_zoomTheta_eq (lam h rc zc : ℝ) (hlam : 0 < lam) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) :
    dr (zoomTheta lam h rc zc u) p
      = (lam ^ (2 * h)) ^ 2 * dr (dz (zoomVRec lam h rc zc u)) p
        - dr (dr (zoomWRec lam h rc zc u)) p := by
  rw [dr]
  have h_event : (fun r : ℝ => zoomTheta lam h rc zc u ((r, p.1.2), p.2))
      =ᶠ[𝓝 p.1.1]
      fun r : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((r, p.1.2), p.2)
        - dr (zoomWRec lam h rc zc u) ((r, p.1.2), p.2) := by
    have hpS : p.1.1 ∈ {r : ℝ | zoomPointRec lam h rc zc ((r, p.1.2), p.2) ∈ unitCylinder} := hp
    filter_upwards [(isOpen_slice_r_rec lam h rc zc p).mem_nhds hpS] with r hr
    exact zoomTheta_eq lam h rc zc hlam u (hu.of_le (by norm_num)) ((r, p.1.2), p.2) hr
  have hnum : HasDerivAt
      (fun r : ℝ => (lam ^ (2 * h)) ^ 2 * dz (zoomVRec lam h rc zc u) ((r, p.1.2), p.2)
        - dr (zoomWRec lam h rc zc u) ((r, p.1.2), p.2))
      ((lam ^ (2 * h)) ^ 2 * dr (dz (zoomVRec lam h rc zc u)) p
        - dr (dr (zoomWRec lam h rc zc u)) p) p.1.1 :=
    ((hasDerivAt_dz_zoomVRec_radial lam h rc zc u hu p hp).const_mul ((lam ^ (2 * h)) ^ 2)).sub
      (hasDerivAt_dr_zoomWRec_radial lam h rc zc u hu p hp)
  exact (hnum.congr_of_eventuallyEq h_event).deriv

end CIV
end
end
