@[expose] public section

open Complex Metric Set

open scoped InnerProductSpace

/-- Smooth Jordan outer approximation holds for every full-dimensional
convex polytope in the complex plane, where a polytope is presented as the
convex hull of a finite set of points. -/
def HasSmoothJordanOuterApproximationForPolytopes : Prop :=
  ∀ u : Finset ℂ,
    (interior (convexHull ℝ (u : Set ℂ))).Nonempty →
      HasSmoothJordanOuterApproximation (convexHull ℝ (u : Set ℂ))

end
