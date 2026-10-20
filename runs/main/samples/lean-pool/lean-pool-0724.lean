@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization

open AVenhance.Infra.Parabolic.FourierGalerkin

open AVenhance.Infra.Torus

local instance classicalSmoothFourierMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance classicalSmoothFourierMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance classicalSmoothFourierProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance classicalSmoothFourierOneLeTwoFact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothFourier.classicalGalerkinFourierMode_derivative_weighted_bound
    (a : ℂ) (k : Fin 2 → ℤ) (n : ℕ) (x : Vec 2) (C : ℝ)
    (hC : (1 + 2 * Real.pi * |(k 0 : ℝ)|) ^ (n + 2) *
        (1 + 2 * Real.pi * |(k 1 : ℝ)|) ^ (n + 2) * ‖a‖ ≤ C) :
    ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => a * AVenhance.Infra.Torus.torusCharacter (-k) y) x‖ ≤
      C * classicalScaledTorusFrequencyWeight k := by
  let u : ℝ := 2 * Real.pi * |(k 0 : ℝ)|
  let v : ℝ := 2 * Real.pi * |(k 1 : ℝ)|
  have hu : 0 ≤ u := by positivity
  have hv : 0 ≤ v := by positivity
  have ha : 0 ≤ ‖a‖ := norm_nonneg _
  have hfreq : 2 * Real.pi * (∑ i : Fin 2, |(k i : ℝ)|) = u + v := by
    simp [u, v, Fin.sum_univ_succ]
    ring
  have hcoeff := classicalWeightedCoeff_frequencyPower_le n u v ‖a‖ C
    hu hv ha (by simpa [u, v] using hC)
  calc
    ‖iteratedFDeriv ℝ n
        (fun y : Vec 2 => a • AVenhance.Infra.Torus.torusCharacter (-k) y) x‖ ≤
      ‖a‖ * (2 * Real.pi * (∑ i : Fin 2, |(k i : ℝ)|)) ^ n :=
      GalerkinSmoothFourier.classicalGalerkinFourierMode_derivative_norm_le a k n x
    _ = ‖a‖ * (u + v) ^ n := by rw [hfreq]
    _ ≤ C * classicalScaledTorusFrequencyWeight k := by
      simpa [u, v, classicalScaledTorusFrequencyWeight] using hcoeff

end AVenhance.Infra.Classical
end
end
