@[expose] public section

noncomputable section

namespace NavierStokes.SlowRecursion

open Set Filter

open scoped Topology ContDiff

/-- Time operator as an element of `AxisFunction R U`. -/
noncomputable def timeOperator {R : ℝ} {U : Set ℂ} {h : ℝ} (c : Domain R U h)
    (b : ℝ) (F : AxisFunction R U) : AxisFunction R U :=
  (-realConstant R U b * F + realConstant R U (1 / 2 - h) * parameter R U *
    parameterDerivative c.open_set F + squaredRadius R U * radialDerivative c.positive c.open_set
        F) *
    inverseDenominator c

end NavierStokes.SlowRecursion
end
end
