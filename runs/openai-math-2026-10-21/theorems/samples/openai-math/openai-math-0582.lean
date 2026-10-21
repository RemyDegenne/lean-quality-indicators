namespace OAI

noncomputable section

open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

open CovarianceCorrector SmoothPeriodicCalculus

lemma unitX_periodic (a : ℝ) : Function.Periodic (unitX a) 1 := by
  intro t
  unfold unitX
  rw [mul_add, mul_one]
  exact reparamX_periodic a _

end ClosedSurfaceR4.CollarVelocity
end
end OAI
