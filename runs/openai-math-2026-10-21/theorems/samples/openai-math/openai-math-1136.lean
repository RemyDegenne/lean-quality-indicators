namespace OAI

noncomputable section

open scoped Classical ContDiff Topology SchwartzMap FourierTransform

open MeasureTheory Filter Set FourierBridge CompletedGauss

namespace SevenEighths.ProbePhysical

lemma gaussianFixedWindow_Vstar_twist (t x : ℝ) (hx : 0<x) :
    Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x=
      gaussianAnnulus x*logPhase t (Real.log x) := by
  have hs : (Real.sqrt x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  unfold Vstar CompletedHeight.normTwistedSource gaussianFixedWindow
  field_simp

end SevenEighths.ProbePhysical
end
end OAI
