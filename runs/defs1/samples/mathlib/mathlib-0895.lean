@[expose] public section

open Filter hiding map_smul

open scoped NNReal Topology Uniformity

variable {𝕜 𝕜₂ 𝕜₃ E Eₗ E' Eₗ' F Fₗ F' Fₗ' G Gₗ G' Gₗ' : Type*}

section SemiNormed

open ContinuousLinearMap

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup Eₗ] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup Fₗ] [SeminormedAddCommGroup G] [SeminormedAddCommGroup Gₗ]

variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Eₗ] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 Fₗ] [NormedSpace 𝕜₃ G]
  [NormedSpace 𝕜 Gₗ] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]

variable
  [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup Eₗ'] [Module 𝕜 Eₗ'] [TopologicalSpace Eₗ'] [IsNormableSpace 𝕜 Eₗ']
  [AddCommGroup F'] [Module 𝕜₂ F'] [TopologicalSpace F'] [IsNormableSpace 𝕜₂ F']
  [AddCommGroup Fₗ'] [Module 𝕜 Fₗ'] [TopologicalSpace Fₗ'] [IsNormableSpace 𝕜 Fₗ']
  [AddCommGroup G'] [Module 𝕜₃ G'] [TopologicalSpace G'] [IsNormableSpace 𝕜₃ G']
  [AddCommGroup Gₗ'] [Module 𝕜 Gₗ'] [TopologicalSpace Gₗ'] [IsNormableSpace 𝕜 Gₗ']

namespace ContinuousLinearMap

variable [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
  [IsNormableSpace 𝕜 E'] [IsTopologicalAddGroup G'] [IsTopologicalAddGroup Gₗ']

variable (E F G σ₁₃ σ₂₃)

variable {E F G σ₁₃ σ₂₃}

variable (𝕜 E Fₗ Gₗ)

variable {𝕜 E Fₗ Gₗ}

variable (F' σ₁₂)

variable [RingHomIsometric σ₁₂] [IsTopologicalAddGroup F'] [IsTopologicalAddGroup Fₗ']

variable {F' σ₁₂}

variable (𝕜 Fₗ') in
/-- The continuous semilinear map obtained by applying a continuous semilinear map at a given
vector.

This is the continuous version of `applyₗ` (and fully continuous version of `LinearMap.applyₗ`). -/
def apply : E' →L[𝕜] (E' →L[𝕜] Fₗ') →L[𝕜] Fₗ' :=
  flip (.id 𝕜 (E' →L[𝕜] Fₗ'))

end ContinuousLinearMap
end SemiNormed
end
