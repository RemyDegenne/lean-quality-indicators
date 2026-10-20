namespace P2MW.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option synthInstance.maxHeartbeats 800000

open MeasureTheory AutomorphicForm AutomorphicForm.SplitPlace Metric Topology Filter Set TopologicalSpace

open scoped TensorProduct TensorProduct.RightActions ContDiff

noncomputable section

namespace P2mSplitFibreSmoothComplex

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.isTopologicalRing_tensor

attribute [local instance] borelSpace_GL t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL

section Coords

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A) (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def coordsHomeo : GL (Fin 2) (L ⊗[K] A) ≃ₜ (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  { (coords A σ ι hdeg hσ).toEquiv with
    continuous_toFun := continuous_coords A σ ι hdeg hσ
    continuous_invFun := continuous_coords_symm A σ ι hdeg hσ }

end Coords
end P2mSplitFibreSmoothComplex
end
end P2MW.S_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_complex
