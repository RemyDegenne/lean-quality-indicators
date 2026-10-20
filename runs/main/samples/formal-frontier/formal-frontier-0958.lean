@[expose] public section

universe uκ uE

noncomputable section

namespace ContinuousLinearMap

section ScalarEnd

variable (κ : Type uκ) [NontriviallyNormedField κ]
  (E : Type uE) [AddCommGroup E] [Module κ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul κ E]

variable [T2Space E] [Module.Invertible κ E]

theorem scalarEndEquiv_symm_smul (A : E →L[κ] E) (v : E) :
    (scalarEndEquiv κ E).symm A • v = A v := by
  rw [← scalarEndEquiv_apply κ E, (scalarEndEquiv κ E).apply_symm_apply]

end ScalarEnd
end ContinuousLinearMap
end
end
