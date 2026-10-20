@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

open Set Function Filter MeasureTheory

open scoped BigOperators ContDiff Topology

namespace NavierStokes.TerminalCompensation

theorem weightedChange_integral (P : Patch) (lam : ℝ) (c : Coeff) (w : ℝ) :
    (∫ x, weightedChange P lam c w x) =
      (∑ j, c j * bumpMoment P (w + slope lam) j) +
        (∑ j, (c j) ^ 2 * squareMoment P w j) / 2 := by
  simp only [funext (weightedChange_identity P lam c w)]
  rw [integral_add (weighted_correction_integrable P (w + slope lam) c)
    ((weighted_correction_sq_integrable P w c).div_const 2), integral_div,
    correction_moment, correction_square_moment]

end NavierStokes.TerminalCompensation
end
end
