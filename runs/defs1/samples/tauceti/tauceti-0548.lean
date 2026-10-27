public section

open Bundle CovariantDerivative Set

open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

variable (I γ s) in
/-- **A geodesic on a parameter set**: a `C²` curve whose covariant acceleration within `s`, taken
for the Levi-Civita connection of the ambient Riemannian bundle instance, vanishes.

The covariant acceleration is `CovariantDerivative.accelerationWithin`, the derivative along the
curve of the velocity `TauCeti.Manifold.curveVelocityWithin`, both taken within `s`. -/
structure IsGeodesicCurveOn : Prop where
  /-- The parameter set has unique derivatives.  Without this the derivatives within `s` are not
  determined by the curve, and the geodesic equation below does not say what it should. -/
  uniqueDiffOn : UniqueDiffOn ℝ s
  /-- A geodesic is `C²` on its parameter set, so the two derivatives in its chart equation are
  genuine within-derivatives. -/
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℝ) I 2 γ s
  /-- **The geodesic equation**: the covariant acceleration vanishes at every parameter of `s`. -/
  accelerationWithin_eq_zero : ∀ r ∈ s, accelerationWithin (leviCivitaConnection I M) γ s r = 0

end TauCeti.Manifold
end
end
