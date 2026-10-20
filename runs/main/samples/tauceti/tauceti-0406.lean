public section

noncomputable section

open Metric Module

open scoped ContDiff Manifold

namespace TauCeti.RiemannianIsometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n k : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]

@[simp]
theorem toLinearIsometryEquiv_symm
    (Φ : RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1)) :
    Φ.symm.toLinearIsometryEquiv = Φ.toLinearIsometryEquiv.symm := by
  apply LinearIsometryEquiv.unitSphereRiemannianIsometry_injective (n := k) (k := n)
  simp [← LinearIsometryEquiv.unitSphereRiemannianIsometry_symm]

end TauCeti.RiemannianIsometry
end
end
