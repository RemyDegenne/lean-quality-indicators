namespace P2MW.S_HeckeEis_range_eichlerShimuraMap_inf_range_conj_eq_bot

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane hiding I

open Complex MvPolynomial

open scoped MatrixGroups ComplexConjugate ModularForm Manifold Pointwise

namespace HeckeEis

namespace ESDisjoint

p2m_open

section Domain

theorem integrableOn_ray {Φ : ℂ → ℂ} (hc : ContinuousOn Φ {z : ℂ | 0 < z.im}) {C δ : ℝ}
    (hδ : 0 < δ) (hb : ∀ z ∈ Ubox, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im)) :
    MeasureTheory.IntegrableOn (fun y : ℝ => Φ (-(1 / 2) + y * Complex.I)) (Set.Ioi (Real.sqrt 3 / 2)) := by
  have hpath : Continuous fun y : ℝ => (-(1 / 2) + y * Complex.I : ℂ) := by fun_prop
  have hcont : ContinuousOn (fun y : ℝ => Φ (-(1 / 2) + y * Complex.I)) (Set.Ioi (Real.sqrt 3 / 2)) :=
    hc.comp hpath.continuousOn fun y hy => im_pos_of_mem_Ubox (ray_mem_Ubox hy)
  refine MeasureTheory.Integrable.mono' ((exp_neg_integrableOn_Ioi _ hδ).const_mul C)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
  have := hb _ (ray_mem_Ubox hy)
  simpa using this

end Domain
end ESDisjoint
end HeckeEis
end
end P2MW.S_HeckeEis_range_eichlerShimuraMap_inf_range_conj_eq_bot
