@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff

open NavierStokes.OutgoingSchedule

namespace NavierStokes.OutgoingTail

theorem tailShape_hasDerivAt (d : TailData) (t : ℝ) :
    HasDerivAt (tailShape d) (tailShapeDeriv d t) t := by
  have hs := (sigma_contDiff.differentiable
      (WithTop.coe_ne_zero.2 ENat.top_ne_zero) ((t - 1) / 2)).hasDerivAt
  have hm := (hs.comp t (((hasDerivAt_id t).sub_const 1).div_const 2)).const_mul d.rho
  convert! hm.const_add (1 - d.rho) using 1; simp only [tailShapeDeriv, one_div]; ring

end NavierStokes.OutgoingTail
end
end
