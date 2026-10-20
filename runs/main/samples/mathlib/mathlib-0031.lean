public section

noncomputable section

open scoped Asymptotics Topology Filter

open Set

namespace Real

variable {x y : ℝ}

theorem hasDerivAt_cosh (x : ℝ) : HasDerivAt cosh (sinh x) x :=
  (Complex.hasDerivAt_cosh x).real_of_complex

end Real
end
end
