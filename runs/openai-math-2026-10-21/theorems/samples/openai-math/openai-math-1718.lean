namespace OAI

noncomputable section

open ContinuousLinearMap

open scoped ContDiff

namespace ContinuumCoulomb

theorem flow_spatial_deriv_eq_full (H : ℝ × Position → Position)
    (hH : ContDiff ℝ 4 H) (t : ℝ) (x e : Position) :
    fderiv ℝ (fun y => H (t,y)) x e = fderiv ℝ H (t,x) (0,e) := by
  have hp : HasFDerivAt (fun y : Position => (t,y)) (inr ℝ ℝ Position) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hc := ((hH.differentiable (by norm_num)) (t,x)).hasFDerivAt.comp x hp
  change fderiv ℝ (H ∘ (fun y : Position => (t,y))) x e = _
  rw [hc.fderiv]
  rfl

end ContinuumCoulomb
end
end OAI
