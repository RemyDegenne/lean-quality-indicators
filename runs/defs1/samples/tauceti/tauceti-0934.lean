public section

open Bundle Manifold CovariantDerivative VectorField Real

open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Sol

local notation "P" => ℝ × ℝ × ℝ

local notation "J" => 𝓘(ℝ, P)

/-- The vector field with constant value `v` in the global coordinates of Sol. -/
def constantField (v : P) (p : Sol) : TangentSpace J p :=
  (tangentSpaceCastModel J p).symm v

end TauCeti.Sol
end
end
