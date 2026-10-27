@[expose] public section

noncomputable section

open NNReal Set Function

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace BoundedContinuousFunction

section NormedSpace

variable {𝕜 : Type*}

variable [TopologicalSpace α] [SeminormedAddCommGroup β]

variable {f g : α →ᵇ β} {x : α} {C : ℝ}

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 β]

section compContinuousCLM

variable {𝕜 : Type*}

section NormedField

variable [TopologicalSpace γ] [NormedField 𝕜] [NormedSpace 𝕜 β]

variable (β 𝕜) in
/-- Precomposition with a continuous map is a continuous linear map from bounded continuous
functions to bounded continuous functions. -/
def compContinuousCLM (g : C(γ, α)) : (α →ᵇ β) →L[𝕜] γ →ᵇ β :=
  LinearMap.mkContinuous
    { toFun f := f.compContinuous g,
      map_add' := by intros; ext; simp,
      map_smul' := by intros; ext; simp }
    1 (by simpa using norm_compContinuous_le · g)

end NormedField
end compContinuousCLM
end NormedSpace
end BoundedContinuousFunction
end
end
