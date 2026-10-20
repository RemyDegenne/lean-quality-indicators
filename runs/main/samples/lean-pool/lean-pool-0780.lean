@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section4

theorem iterate_material_majorant_constant_nonneg (Ccoef Cs Cv Cf : ℝ) :
    0 ≤ amnrMaterialMajorantConstant Ccoef Cs Cv Cf := by
  unfold amnrMaterialMajorantConstant
  positivity

end AVenhance.Infra.Section4
end
end
