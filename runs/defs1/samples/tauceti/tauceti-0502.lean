public section

open Function Set

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M}

/-- A vector field `X` is a **pseudo-gradient field adapted to `f`** when it is smooth, `f`
strictly decreases along it away from the critical points (`d f_x (X x) < 0`, with the differential
read in `ℝ` through `mvfderiv`), and near each critical point there is a Morse chart in which it is
the negative gradient `z ↦ (-wᵢ zᵢ)ᵢ` of the quadratic normal form `(1/2) Σᵢ wᵢ zᵢ²`. -/
structure IsAdaptedPseudoGradient (f : M → ℝ) (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) : Prop where
  contMDiff : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
    (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M))
  mvfderiv_apply_lt_zero : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0 → mvfderiv 𝓘(ℝ, E) f x (X x) < 0
  exists_morseChart : ∀ x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 →
    ∃ φ : MorseChart E f x, ∀ y ∈ φ.toChart.source,
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)

end TauCeti
end
