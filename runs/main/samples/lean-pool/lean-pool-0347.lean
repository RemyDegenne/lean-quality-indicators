section

@[expose] public section

noncomputable section

namespace NavierStokes.SmoothFamilyTorusInverse

open Set Filter MeasureTheory TorusInverse

open scoped Topology ContDiff BigOperators

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

open ParametricTorusInverse (PolynomialGrowth multiplierX multiplierY)

section FiniteDimensional

variable [FiniteDimensional ℝ P]

theorem multiplierJetConstant_nonneg (n l : ℕ) : 0 ≤ multiplierJetConstant (P := P) n l := by
  induction n generalizing l with
  | zero => unfold multiplierJetConstant; positivity
  | succ n ih =>
      rw [multiplierJetConstant]
      exact add_nonneg (mul_nonneg (Finset.sum_nonneg fun i hi => by positivity) (ih l))
        (mul_nonneg (by positivity) (ih (l + 1)))

end FiniteDimensional
end NavierStokes.SmoothFamilyTorusInverse
end
end
end
