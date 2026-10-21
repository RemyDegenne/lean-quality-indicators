namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem wordWeight_turnUnits (w : List Bool) :
    wordWeight w = (criticalActivity : ℂ) ^ w.length *
      Complex.exp (((Real.pi / 8) * (turnUnits w : ℝ) : ℝ) * Complex.I) := by
  rw [wordWeight_physical,turnAngle_sum]
  congr 2
  push_cast
  ring

end PolynomialVacuumBridge.Corridor
end
end OAI
