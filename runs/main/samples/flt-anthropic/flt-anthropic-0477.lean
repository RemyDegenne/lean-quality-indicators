namespace P2MW.S_AutomorphicForm_RealIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc

open Set MeasureTheory

open scoped Topology

set_option autoImplicit false

noncomputable section

namespace Ws31

namespace ArchR

theorem clause_a (k : ℤ) (t : ℝ) (ht : t ≠ 0) : AnalyticOnNhd ℂ (fun w : ℂ => Jg k w t) Set.univ := by
  refine DifferentiableOn.analyticOnNhd (fun w₀ _ => ?_) isOpen_univ
  apply DifferentiableAt.differentiableWithinAt
  have hmem : H (nw w₀) ∈ 𝓝 w₀ := (isOpen_H _).mem_nhds (mem_H_nw w₀)
  have hd : DifferentiableAt ℂ (fun w => J (nw w₀) k w t) w₀ :=
    (J_differentiableOn _ k t ht).differentiableAt hmem
  refine hd.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem hmem (fun w hw => Jg_eq k hw ht)

end ArchR
end Ws31
end
end P2MW.S_AutomorphicForm_RealIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc
