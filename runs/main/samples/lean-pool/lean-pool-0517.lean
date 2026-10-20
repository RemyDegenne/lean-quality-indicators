@[expose] public section

namespace Vlasov

open MeasureTheory ENNReal

lemma IsLagrangianVlasovSolutionOn.mono_window
    {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d} {g : ℝ → Measure (PhaseSpace d)}
    {T T' : ℝ} (h : IsLagrangianVlasovSolutionOn gradW g T) (hTT' : T' ≤ T) :
    IsLagrangianVlasovSolutionOn gradW g T' := by
  obtain ⟨h_sol, charX, charV, h_flow, h_push, h_aemeas, h_cont⟩ := h
  refine ⟨?_, charX, charV, ?_, ?_, ?_⟩
  · intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s hs
    exact h_sol φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ s
      ⟨hs.1, lt_of_lt_of_le hs.2 hTT'⟩
  · exact h_flow.mono (Set.Ioo_subset_Ioo le_rfl hTT') Set.Subset.rfl
  · intro s hs; exact h_push s ⟨hs.1, le_trans hs.2 hTT'⟩
  · refine ⟨?_, ?_⟩
    · intro s hs; exact h_aemeas s ⟨hs.1, le_trans hs.2 hTT'⟩
    · intro z; exact (h_cont z).mono (fun u hu => ⟨hu.1, le_trans hu.2 hTT'⟩)

end Vlasov
end
