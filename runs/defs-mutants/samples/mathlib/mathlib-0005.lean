@[expose] public section

noncomputable section

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry AffineMap

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

variable {V₂ P₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MetricSpace P₂]

variable [NormedAddTorsor V₂ P₂]

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
def altitude {n : ℕ} (s : Simplex ℝ P n) (i : Fin (n + 1)) : AffineSubspace ℝ P :=
  mk' (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)).directionᗮ ⊓
    affineSpan ℝ (Set.range s.points)

end Simplex
end Affine
end
end
