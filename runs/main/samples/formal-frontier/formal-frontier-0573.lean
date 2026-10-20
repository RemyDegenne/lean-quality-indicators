@[expose] public section

open scoped ContDiff Manifold

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

variable {H : Type v} [TopologicalSpace H]

variable (I : ModelWithCorners ℂ E H) [I.Boundaryless]

variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

theorem isManifold_infty_of_differentiableOn_chartTransitions
    (h : ∀ e e' : OpenPartialHomeomorph M H,
      e ∈ atlas H M → e' ∈ atlas H M →
      DifferentiableOn ℂ (I ∘ (e.symm ≫ₕ e') ∘ I.symm)
        (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ Set.range I)) :
    IsManifold I ∞ M := by
  have : IsManifold I ω M := isManifold_omega_of_differentiableOn_chartTransitions I h
  exact IsManifold.of_le le_top

end
