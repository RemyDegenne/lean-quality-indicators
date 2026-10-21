namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem GammaEnvironment.ae_localPassageTime_gap_indicator
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    ∀ᵐ ω ∂P,
      0 ≤ FiniteLocal.passageTime (fun e => τ e ω) p q R -
        PlanarFPP.passageTime (fun e => τ e ω) p q ∧
      FiniteLocal.passageTime (fun e => τ e ω) p q R -
        PlanarFPP.passageTime (fun e => τ e ω) p q ≤
      {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
        PlanarFPP.passageTime (fun e => τ e ω) p q}.indicator
          (fun ω => pathCost (fun e => τ e ω) p (coordinatePath p q)) ω := by
  filter_upwards [h.ae_positive_edges] with ω hpos
  have hw : ∀ e, 0 ≤ τ e ω := fun e => (hpos e).le
  have hlo := FiniteLocal.unrestricted_passageTime_le (fun e => τ e ω) hw p q R hR
  have hup := FiniteLocal.passageTime_le_coordinatePath (fun e => τ e ω) hw p q R hR
  have ht := PlanarFPP.passageTime_nonneg (fun e => τ e ω) hw p q
  refine ⟨sub_nonneg.mpr hlo, ?_⟩
  by_cases he : FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q
  · have hmem : ω ∈ {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
        PlanarFPP.passageTime (fun e => τ e ω) p q} := he
    rw [Set.indicator_of_mem hmem]
    linarith
  · have heq := not_ne_iff.mp he
    simp [heq]

end GammaFPP
end OAI
