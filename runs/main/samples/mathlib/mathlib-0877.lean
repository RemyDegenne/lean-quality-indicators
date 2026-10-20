public section

open Set Function Filter

open scoped Topology

lemma strictMonoOn_of_hasDerivWithinAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, 0 < f' x) : StrictMonoOn f D :=
  strictMonoOn_of_deriv_pos hD hf fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

end
