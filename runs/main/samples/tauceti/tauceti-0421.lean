public section

open TensorProduct TauCeti

namespace ContinuousAlternatingMap

variable {E F₁ F₂ F₃ : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
  [AddCommGroup F₃] [Module ℝ F₃] [TopologicalSpace F₃]
  [IsTopologicalAddGroup F₃] [ContinuousSMul ℝ F₃]

theorem pairedWedge_apply {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hμ : Continuous (Function.uncurry fun x y ↦ μ x y))
    (φ : E [⋀^Fin k]→L[ℝ] F₁) (ψ : E [⋀^Fin l]→L[ℝ] F₂)
    (v : Fin (k + l) → E) :
    pairedWedge μ hμ φ ψ v =
      (((k.factorial : ℝ) * (l.factorial : ℝ))⁻¹) •
        ∑ σ : Equiv.Perm (Fin (k + l)), Equiv.Perm.sign σ •
          μ (φ (fun i ↦ v (σ (Fin.castAdd l i))))
            (ψ (fun j ↦ v (σ (Fin.natAdd k j)))) := by
  simp only [pairedWedge, ContinuousAlternatingMap.smul_apply,
    ContinuousMultilinearMap.alternatization_apply_apply,
    wedgeWithUnalternatedContinuous_apply]
  simp only [Function.comp_apply]

end ContinuousAlternatingMap
end
