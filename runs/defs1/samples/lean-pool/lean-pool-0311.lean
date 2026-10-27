section

@[expose] public section

noncomputable section

namespace NavierStokes.AxisContraction

open Set Metric

open scoped NNReal ContDiff

variable {E F G H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A finite threshold depending only on fixed operator/coefficient data,
the reference pair, and the uniform norm bound M. In particular it does
not depend on the normalized amplitude a. -/
def contractionThreshold (O : NaturalOperators V) (d : AxisData V)
    (S : V →L[ℝ] V) (x₀ : V × V) (M : ℝ) (hM : 0 ≤ M) : ℝ :=
  1 + remainderBound O d S (‖x₀‖ + 1) M (by positivity) hM +
    remainderLip O d S (‖x₀‖ + 1) M (by positivity) hM

end NavierStokes.AxisContraction
end
end
end
