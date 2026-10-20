@[expose] public section

open Complex Set Metric Filter Topology MeasureTheory

namespace RectHomotopyProof

lemma winding_fdPolygon_eq_circleParamCW (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1 / 2) (hp_im_pos : 0 < p.im) (hp_im : p.im < HHeight) :
    generalizedWindingNumber' fdPolygon 0 5 p =
    generalizedWindingNumber' (circleParamCW p 1 0 5) 0 5 p := by
  rw [winding_fdPolygon_eq_radialCircle p hp_norm hp_re hp_im,
      winding_radialCircle_eq_circleParamCW p hp_norm hp_re hp_im_pos hp_im]

end RectHomotopyProof
end
