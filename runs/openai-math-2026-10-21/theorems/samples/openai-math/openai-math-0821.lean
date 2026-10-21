namespace OAI

section

section

namespace DilutedSpinGlass.UniversalDictionary

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir Filter Set

open scoped NNReal BigOperators Topology

variable {L p : ℕ}

theorem singleton_average_selection (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H)
    (hθi : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hhi : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ), StrictMono Ns ∧
      (∀ n i, us n i ∈ Icc (probeLow i.2) (probeHigh i.2)) ∧
      (∀ n, ConcreteReservoir.increment (weights L) prior (gridExponents L) direction anchor M (Ns n) (us n) ≤
        liminf (pressure M) atTop+ε) ∧
      (∀ η : ℝ, 0 < η → ∀ t : ℝ, 0 < t → ∀ᶠ n in atTop,
        regularSingletonAverage M C H (Ns n+1) (us n) η ≤ ((L+1:ℕ):ℝ)⁻¹/η+t) := by
  obtain ⟨Ns,us,hNs,hus,hinc,he⟩ := singleton_grid_selection M hC hH hθ hh hθi hhi hε
  refine ⟨Ns,us,hNs,hus,hinc,?_⟩
  intro η hη t ht
  filter_upwards [he η hη t ht] with n hn
  exact regularSingletonAverage_le M C H (Ns n+1) (us n) η _ (by positivity) hn

end DilutedSpinGlass.UniversalDictionary
end
end
end OAI
