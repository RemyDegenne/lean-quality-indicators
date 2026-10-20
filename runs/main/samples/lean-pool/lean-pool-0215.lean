section

@[expose] public section

noncomputable section

namespace NavierStokes.StressAlgebra

open MeasureTheory Set

theorem angular_integrated_identity
    {h η X : ℝ} (p : AngularMomentData h η X)
    (hint : IntervalIntegrable
      (fun x => angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x))
      volume 0 X) :
    intervalIntegral
      (fun x => angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x))
      0 X volume =
      angularPrimitive h η p.W p.H p.I p.Iη p.J p.Jη X := by
  have hd : ∀ x ∈ uIcc 0 X,
      HasDerivAt (angularPrimitive h η p.W p.H p.I p.Iη p.J p.Jη)
        (angularSource h η x (p.W x) (p.U x) (p.H x) (p.Hx x) (p.Hη x)) x := by
    intro x hx
    exact angularPrimitive_hasDerivAt h η x p.W p.H p.I p.Iη p.J p.Jη
      (p.Wx x) (p.Hx x) (p.U x) (p.Uη x) (p.Hη x)
      (p.W_deriv x hx) (p.H_deriv x hx) (p.I_deriv x hx) (p.Iη_deriv x hx)
      (p.J_deriv x hx) (p.Jη_deriv x hx) (p.W_balance x hx)
  have hzero : angularPrimitive h η p.W p.H p.I p.Iη p.J p.Jη 0 = 0 := by
    simp [angularPrimitive, p.I_zero, p.Iη_zero, p.J_zero, p.Jη_zero]
  simpa only [hzero, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint

end NavierStokes.StressAlgebra
end
end
end
