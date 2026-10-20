@[expose] public section

noncomputable section

open MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps

namespace StationaryHarmonicMap

theorem deriv_thetaFactor {n : ℕ} {rho : ℝ} :
    deriv (thetaFactor n) rho =
      ((2 : ℝ) - (n : ℝ)) * rho ^ (1 - (n : ℤ)) := by
  have hcast : (((2 - (n : ℤ) : ℤ) : ℝ)) = (2 : ℝ) - (n : ℝ) := by
    norm_num
  have hexp : (2 - (n : ℤ) : ℤ) - 1 = 1 - (n : ℤ) := by
    omega
  unfold thetaFactor
  rw [deriv_zpow, hcast, hexp]

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps
end
end
