public section

namespace TauCeti

open MeasureTheory TopologicalSpace

open scoped ContDiff Distributions

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {v : E}

section Basis

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {u : E → F}

theorem _root_.Module.Basis.hasWeakFDerivOn_of_forall {ι : Type*} [CompleteSpace F]
    (b : Module.Basis ι ℝ E) {U : E → E →L[ℝ] F} (hu : LocallyIntegrableOn u Ω μ)
    (h : ∀ i, HasWeakLineDerivOn μ Ω u (fun x => U x (b i)) (b i)) :
    HasWeakFDerivOn μ Ω u U := by
  classical
  intro y
  have hy : ∑ i ∈ (b.repr y).support, b.repr y i • b i = y := by
    have hrepr := b.linearCombination_repr y
    rwa [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
  have key : HasWeakLineDerivOn μ Ω u
      (fun x => ∑ i ∈ (b.repr y).support, b.repr y i • U x (b i))
      (∑ i ∈ (b.repr y).support, b.repr y i • b i) :=
    HasWeakLineDerivOn.sum_direction _ hu fun i _ => by
      simpa [Pi.smul_def] using (h i).smul_direction (b.repr y i)
  have hval : ∀ x, (∑ i ∈ (b.repr y).support, b.repr y i • U x (b i)) = U x y := by
    intro x
    have hUy : U x y = U x (∑ i ∈ (b.repr y).support, b.repr y i • b i) := by rw [hy]
    rw [hUy, map_sum]
    simp
  rw [hy] at key
  exact key.congr_ae_deriv (Filter.Eventually.of_forall hval)

end Basis
end TauCeti
end
