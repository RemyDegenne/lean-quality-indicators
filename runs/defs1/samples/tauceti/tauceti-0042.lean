public section

noncomputable section

open MeasureTheory Set TopologicalSpace

open scoped ENNReal NNReal ContDiff Gradient

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)}
  {φ : E → ℝ} {a b : ℝ} {ψ : WithLp 2 (ℝ × E) → ℝ} {M : ℝ}

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Sobolev extension through a Lipschitz boundary chart.** For a Lipschitz boundary chart of
`Ω` with coordinates `e`, graph `φ` and radii `a`, `b`, and a smooth cutoff `ψ` whose support has
chart coordinates in the shortened cylinder `normalCylinder (a - 2 * L * b) b`, the operator
sends `u ∈ W^{1,p}(Ω)` to a whole-space Sobolev function equal to `ψ u` on `Ω`
(`TauCeti.W1p.restrictL_lipschitzChartExtensionL`): multiply by the cutoff, extend across the
graph by reflection in flattened chart coordinates, and return to the original coordinates. -/
def W1p.lipschitzChartExtensionL
    (h : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzChartWith L e φ a b)
    (ψ : WithLp 2 (ℝ × E) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hM : 0 ≤ M)
    (hψM : ∀ x ∈ Ω, |ψ x| ≤ M) (hgM : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ M)
    (hs : tsupport ψ ⊆ e ⁻¹' normalCylinder (a - 2 * L * b) b) :
    W1p volume Ω p →L[ℝ] W1p volume (⊤ : Opens (WithLp 2 (ℝ × E))) p :=
  (W1p.compAffineIsometryEquivL e (by simp)).comp <|
    (W1p.normalEpigraphExtensionL (φ := ⟨φ, _⟩) h.lipschitzWith).comp <|
    W1p.lipschitzChartLocalizeL h ψ hψ hM hψM hgM
      (hs.trans (preimage_mono (normalCylinder_sub_subset h)))

end TauCeti
end
end
