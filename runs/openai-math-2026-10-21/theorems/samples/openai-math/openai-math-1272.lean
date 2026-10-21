namespace OAI

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure Real ProbabilityTheory

open scoped ENNReal NNReal Topology Pointwise

namespace GeneralMahler

section

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedAddCommGroup E] [NormedAddCommGroup F]

section Integrals

variable [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsAddHaarMeasure μ]

lemma mixed_integrable_left {f : X → Y → E}
    (h : mixed f) (y : Y) (hf : AEStronglyMeasurable (fun x => f x y) μ) :
    Integrable (fun x => f x y) μ := by
  obtain ⟨C,l,hc,H⟩ := h (Module.finrank ℝ X+1)
  refine ((envelope_inv_int (X := X)).const_mul (C*(1+‖y‖)^l)).mono' hf (ae_of_all _ fun x => ?_)
  rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]; apply H

end Integrals
end
end GeneralMahler
end
end OAI
