public section

open Set Filter Topology

open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

theorem hasDerivAt_zoomRec_component_z (lam h rc zc : ℝ) {u : ParabolicPoint → Vec3}
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (p : (ℝ × ℝ) × ℝ) (hp : zoomPointRec lam h rc zc p ∈ unitCylinder) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => u (zoomPointRec lam h rc zc ((p.1.1, s), p.2)) i)
      (lam ^ (1 - 2 * h) * spatialPartial (fun w => u w i) 2 (zoomPointRec lam h rc zc p))
      p.1.2 :=
  hasDerivAt_comp_spatialSlice hu hp
    (hasDerivAt_meridional_snd (rc + lam * p.1.1) zc (lam ^ (1 - 2 * h)) p.1.2) rfl i

end CIV
end
end
