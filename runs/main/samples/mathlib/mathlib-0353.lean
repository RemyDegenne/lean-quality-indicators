@[expose] public section

variable {α R 𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃]
  {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₃ →+* 𝕜₂} {D E F G : Type*}
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]

namespace PointwiseConvergenceCLM

section NormedSpace

variable [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]

lemma withSeminorms : WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F) :=
  let e : E ≃ (Σ _ : E, Unit) := .symm <| .sigmaUnique _ _
  (isInducing_inducingFn σ E F).withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ F)
    |>.congr_equiv e

end NormedSpace
end PointwiseConvergenceCLM
end
