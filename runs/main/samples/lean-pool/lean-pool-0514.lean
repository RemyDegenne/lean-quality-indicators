section

@[expose] public section

noncomputable section

namespace NavierStokes.TorusInverse

open scoped BigOperators Topology ContDiff

open MeasureTheory

local instance instTorusInverse1 : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

theorem mode_eq_torusMode (k : Frequency) (x : Plane) :
    mode k x = torusMode k ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle)) := by
  change Complex.exp (phase k x) =
    fourier k.1 (x.1 : UnitAddCircle) * fourier k.2 (x.2 : UnitAddCircle)
  rw [phase_formula, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_one, div_one, omega]
  ring

end NavierStokes.TorusInverse
end
end
end
