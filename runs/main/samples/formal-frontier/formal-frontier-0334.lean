public section

set_option warningAsError true

noncomputable section

open GeneralLinearCoordinateRing

universe u

namespace AlgebraicGeometry

variable (K : Type u) [Field K] (n : Type u) [Fintype n] [DecidableEq n]

theorem generalLinearCoordinateRing_ringKrullDim :
    ringKrullDim (GeneralLinearCoordinateRing.CoordinateRing K n) =
      ((Fintype.card n ^ 2 : ℕ) : WithBot ℕ∞) :=
  dimension_gl K n

end AlgebraicGeometry
end
end
