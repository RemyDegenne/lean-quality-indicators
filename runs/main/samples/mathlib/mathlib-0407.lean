@[expose] public section

noncomputable section

namespace Complex

variable {z : ℂ}

open Topology Filter

open scoped ComplexConjugate

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

open ContinuousLinearMap

@[simp]
theorem ofRealCLM_coe : (ofRealCLM : ℝ →ₗ[ℝ] ℂ) = ofRealAm.toLinearMap :=
  rfl

end Complex
end
end
