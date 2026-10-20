@[expose] public section

open MeasureTheory Finset

open scoped ENNReal

noncomputable
section

namespace Malliavin

variable {T : Type*} {E : Type*}

section InnerProduct

variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_eq_norm_sq_symmetrizeL_add (n : ℕ)
    (f : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    ‖f‖ ^ 2 = ‖symmetrizeL E (μ := μ) n 2 f‖ ^ 2 + ‖f - symmetrizeL E (μ := μ) n 2 f‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (symmetrizeL E (μ := μ) n 2 f)
    (f - symmetrizeL E (μ := μ) n 2 f) (inner_symmetrizeL_sub_symmetrizeL n f)
  rw [add_sub_cancel] at h
  simpa only [sq] using h

end InnerProduct
end Malliavin
end
end
