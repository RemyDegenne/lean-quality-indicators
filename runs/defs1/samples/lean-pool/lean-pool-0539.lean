@[expose] public section

noncomputable section

namespace NavierStokes.MeanIncrementBounds

open Set Filter WeightedClasses

open scoped ContDiff Topology

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

namespace Operators

/-- The connection parameter is one for radial/angular velocity, zero axially. -/
noncomputable def viscosity (o : Operators D) (c : ℝ) (f : Field D) : Field D :=
  fun n x => o.epsilon n *
    (o.dr (o.dr f) n x + o.invRadius n x * o.dr f n x +
      o.dz (o.dz f) n x - c * (o.invRadius n x * (o.invRadius n x * f n x)))

end Operators
end NavierStokes.MeanIncrementBounds
end
end
