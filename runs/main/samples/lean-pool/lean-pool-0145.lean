@[expose] public section

namespace Vlasov

open MeasureTheory ENNReal

lemma IsLagrangianVlasovSolution.toOn {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d}
    {f : ℝ → Measure (PhaseSpace d)}
    (h : IsLagrangianVlasovSolution gradW f) (T : ℝ) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  obtain ⟨h_sol, charX, charV, h_flow, h_push, h_meas⟩ := h
  refine ⟨h_sol.toOn T, charX, charV, ?_, ?_, ?_, ?_⟩
  · -- IsCharacteristicFlowOn from IsCharacteristicFlow.
    exact ⟨fun z _ => h_flow.1 z,
           fun t _ z _ => h_flow.2.1 t z,
           fun t _ z _ => h_flow.2.2 t z⟩
  · intro t _; exact h_push t
  · intro s _; exact h_meas s
  · -- Boundary ContinuousOn from universal HasDerivAt → continuity everywhere.
    intro z
    have hX : Continuous (fun s => charX s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.1 t z).continuousAt)
    have hV : Continuous (fun s => charV s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.2 t z).continuousAt)
    exact (hX.prodMk hV).continuousOn

end Vlasov
end
