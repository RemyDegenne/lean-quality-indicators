public section

namespace MeasureTheory.Integrable

variable {G E : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] {μ : Measure G} [μ.IsAddRightInvariant] {f : G → E}

theorem setIntegral_norm_comp_sub_sub_le (hf : Integrable f μ) (h : G) :
    ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f (x - h) - f x‖ ∂μ ≤
      2 * ∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ := by
  have hST : {x : G | 2 * ‖h‖ < ‖x‖} ⊆ {x | ‖h‖ < ‖x‖} :=
    Set.ofPred_subset_ofPred.2 fun x hx ↦ by linarith [norm_nonneg h]
  calc ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f (x - h) - f x‖ ∂μ
      ≤ ∫ x in {x | 2 * ‖h‖ < ‖x‖}, (‖f (x - h)‖ + ‖f x‖) ∂μ :=
        setIntegral_mono ((hf.comp_sub_right h).sub hf).norm.integrableOn
          ((hf.comp_sub_right h).norm.add hf.norm).integrableOn fun x ↦ norm_sub_le _ _
    _ = (∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f (x - h)‖ ∂μ) + ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f x‖ ∂μ :=
        integral_add (hf.comp_sub_right h).norm.integrableOn hf.norm.integrableOn
    _ ≤ (∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ) + ∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ := by
        gcongr ?_ + ?_
        · exact hf.setIntegral_norm_comp_sub_le h
        · exact setIntegral_mono_set hf.norm.integrableOn (.of_forall fun _ ↦ norm_nonneg _)
            (.of_forall hST)
    _ = 2 * ∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ := by ring

end MeasureTheory.Integrable
end
