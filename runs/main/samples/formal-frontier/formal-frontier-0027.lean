@[expose] public section

noncomputable section

open scoped unitInterval

namespace AddCircle

theorem eq_loop_fundamentalGroupEquivInt {T : ℝ} (hT : T ≠ 0)
    (γ : FundamentalGroup (AddCircle T) 0) :
    γ = FundamentalGroup.fromPath ⟦loop T (fundamentalGroupEquivInt hT γ).toAdd⟧ := by
  exact ((fundamentalGroupEquivInt hT).symm_apply_apply γ).symm.trans
    (fundamentalGroupEquivInt_symm_apply hT _)

end AddCircle
end
end
