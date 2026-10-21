namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

theorem realification_ker (f : V →ₗ[ℚ] W) :
    (LinearMap.ker f).baseChange ℝ = LinearMap.ker (f.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  have h : Function.Exact ((LinearMap.ker f).subtype.baseChange ℝ) (f.baseChange ℝ) :=
    Module.Flat.lTensor_exact ℝ f.exact_subtype_ker_map
  exact (LinearMap.exact_iff.mp h).symm

end Erdos3
end
end OAI
