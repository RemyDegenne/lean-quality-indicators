@[expose] public section

namespace NavierStokes.CylindricalResidual

noncomputable section

open ProblemStatement Filter

open AxisymmetricFields (projection)

open AxisymmetricResidual (pack pack_zero pack_one pack_two packDerivative
  packDerivative_apply hasFDerivAt_pack)

open scoped BigOperators ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Vector advection, given by `w q 0 • dCoord 0 w q + (w q 1 / q 0) • (dCoord 1 w q +
connection (w q)) + w q 2 • dCoord 2 w q`. -/
noncomputable def vectorAdvection (w : Space → Space) (q : Space) : Space :=
  w q 0 • dCoord 0 w q + (w q 1 / q 0) • (dCoord 1 w q + connection (w q)) +
    w q 2 • dCoord 2 w q

end
end NavierStokes.CylindricalResidual
end
