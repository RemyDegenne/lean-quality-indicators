public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

@[simp]
theorem schwarzChristoffelFiniteEdge_of_integrable_logarithmic (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ}
    (hp : -1 < ∑ i with a i = p, e i) (hq : ∑ i with a i = q, e i = -1) :
    schwarzChristoffelFiniteEdge a e z₀ p q =
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ p +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' Ici 0 := by
  simp [schwarzChristoffelFiniteEdge, hp, hq]

end TauCeti
end
end
