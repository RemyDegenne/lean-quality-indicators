public noncomputable section

open UpperHalfPlane MatrixGroups ModularForm Matrix.SpecialLinearGroup Filter Topology Function Set

open scoped Manifold MatrixGroups

namespace TauCeti.ModularForm

/-- The normalized modular invariant `j = E₄³ / Δ` on the upper half-plane. -/
def j (z : ℍ) : ℂ := E₄ z ^ 3 / discriminant z

end TauCeti.ModularForm
end
