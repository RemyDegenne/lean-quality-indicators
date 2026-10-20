@[expose] public section

open CategoryTheory CategoryTheory.Limits ContinuousMap

open scoped ContinuousMap

noncomputable section

namespace SphereTopology

/-- Real Euclidean three-space, with coordinate order `(x, y, z)`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end SphereTopology
end
end
