public section

namespace TauCeti

namespace ContinuousAlternatingMap

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The alternatization `B ↦ ((v₀, v₁) ↦ B v₀ v₁ - B v₁ v₀)` of a continuous bilinear map, as a
continuous linear map into the continuous alternating two-forms. It is Mathlib's
`ContinuousAlternatingMap.alternatizeUncurryFinCLM` in one alternating argument, precomposed with
the identification of `E →L[𝕜] F` with the continuous alternating maps in one argument. -/
noncomputable def alternatizeBilinCLM : (E →L[𝕜] E →L[𝕜] F) →L[𝕜] E [⋀^Fin 2]→L[𝕜] F :=
  (ContinuousAlternatingMap.alternatizeUncurryFinCLM 𝕜 E F).comp
    (ContinuousLinearMap.compL 𝕜 E (E →L[𝕜] F) (E [⋀^Fin 1]→L[𝕜] F)
      ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := F)
        (0 : Fin 1)).toContinuousLinearEquiv : (E →L[𝕜] F) →L[𝕜] E [⋀^Fin 1]→L[𝕜] F))

end ContinuousAlternatingMap
end TauCeti
end
