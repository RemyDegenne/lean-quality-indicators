@[expose] public section

open Function MeasureTheory Set

open scoped ENNReal

namespace QuadraticCarleson

theorem krauseLaceySignedLocalizedPiece_support_subset
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ)
    (hscale : I.length = (2 : ℝ) ^ (j + 2)) :
    Function.support (krauseLaceySignedLocalizedPiece lam j I f) ⊆ I.carrier := by
  intro x hx
  by_contra hmem
  exact hx (krauseLaceySignedLocalizedPiece_eq_zero_of_notMem lam j I f hscale hmem)

end QuadraticCarleson
end
