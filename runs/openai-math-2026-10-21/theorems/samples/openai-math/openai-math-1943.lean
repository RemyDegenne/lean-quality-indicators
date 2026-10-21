namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp]
theorem hyperplaneRetraction_on_kernel (f : E →ₗ[ℝ] ℝ) (w : E) (hw : f w = 1) (x : f.ker) :
    hyperplaneRetraction f w hw (x : E) = x := by
  apply Subtype.ext
  simp only [hyperplaneRetraction_coe, LinearMap.mem_ker.mp x.property, zero_smul, sub_zero]

end Erdos3
end
end OAI
