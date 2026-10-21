namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Matrix

noncomputable section

open scoped Matrix ComplexOrder

noncomputable section

open scoped TensorProduct InnerProductSpace BigOperators

noncomputable section

open scoped BigOperators ComplexConjugate

noncomputable section

open scoped InnerProductSpace

namespace SpinAngle.TensorRep

variable {ι n : Type*} [contextInstance1770_23 : Fintype ι] [contextInstance1770_35 : DecidableEq ι] [contextInstance1770_51 : Fintype n] [contextInstance1770_63 : DecidableEq n]

lemma continuous_rep : Continuous (fun g : Matrix.unitaryGroup n ℂ =>
    (rep (ι := ι) g).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (continuous_action v).comp continuous_subtype_val

end SpinAngle.TensorRep
end
end
end
end
end
end
end OAI
