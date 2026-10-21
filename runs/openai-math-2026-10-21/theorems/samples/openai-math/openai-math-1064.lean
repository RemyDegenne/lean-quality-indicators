namespace OAI

namespace DFVSGames.Repetition.ProjectionKernel

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem exists_energy_le_deterministicVector [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) (hh : ∀ x a, 0 ≤ h x a) :
    ∃ labels : Q₁ → A₁,
      K.energy h ≤ K.energy (deterministicVector h labels) := by
  classical
  obtain ⟨labels, _, _, hlabels⟩ := exists_deterministic_vector h hh
    (fun t : Q₂ × A₂ => K.outer.weight t.1)
    (fun t => K.outer.nonnegative t.1) K.linearCoefficient
  refine ⟨labels, ?_⟩
  rw [K.energy_eq_linearCoefficient_sum, K.energy_eq_linearCoefficient_sum]
  exact hlabels

end
end DFVSGames.Repetition.ProjectionKernel
end OAI
