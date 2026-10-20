namespace P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open Set Real

noncomputable section

open MeasureTheory Set Real

noncomputable section

namespace K7RB3bRed

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

local notation "μ3" => Measure.prod (volume : Measure ℝ) (Measure.prod (volume : Measure ℝ)
  (Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))))

theorem ae_snd_ne_zero : ∀ᵐ q : ℝ × ℝ × ℝ ∂μ3, q.2.1 ≠ 0 := by
  have h0 : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ 0 := by
    have : ({0}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [this] with x hx
    simpa using hx
  have hB : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))), p.1 ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst).ae h0
  exact (Measure.quasiMeasurePreserving_snd).ae hB

end K7RB3bRed
end
end
end P2MW.S_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets
