public section

noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace

open scoped NNReal

variable {K : Type*} [Field K]

namespace TauCeti.GlobalNumberFields

variable [NumberField K]

@[simp]
theorem coe_ideleNorm_ofCompletion (w : InfinitePlace K) (u : w.Completionˣ) :
    ((ideleNorm (IdeleGroup.ofCompletion (𝓞 K) K w u) : ℝ≥0) : ℝ) =
      completionNormalizedAbsValue w u := by
  rw [coe_ideleNorm, Finset.prod_eq_single w (fun w' _ hw' ↦ by
    simp [w'.ideleInfiniteCoord_ofCompletion_of_ne hw']) (by simp)]
  simp

end TauCeti.GlobalNumberFields
end
end
