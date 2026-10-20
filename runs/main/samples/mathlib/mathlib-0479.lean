@[expose] public section

open Function Set Metric

variable (𝕜 : Type*) {V V₁ V₂ V₃ : Type*} {P₁ : Type*} (P P₂ : Type*) {P₃ : Type*}
  [NormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [PseudoMetricSpace P] [NormedAddTorsor V P]
  [SeminormedAddCommGroup V₁] [NormedSpace 𝕜 V₁] [PseudoMetricSpace P₁] [NormedAddTorsor V₁ P₁]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₂] [PseudoMetricSpace P₂] [NormedAddTorsor V₂ P₂]
  [SeminormedAddCommGroup V₃] [NormedSpace 𝕜 V₃] [PseudoMetricSpace P₃] [NormedAddTorsor V₃ P₃]

variable {𝕜 P P₂}

@[inherit_doc]
notation:25 -- `→ᵃᵢ` would be more consistent with the linear isometry notation, but it is uglier
P " →ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometry 𝕜 P P₂

variable (𝕜 P P₂)

variable {𝕜 P P₂}

@[inherit_doc] notation:25 P " ≃ᵃⁱ[" 𝕜:25 "] " P₂:0 => AffineIsometryEquiv 𝕜 P P₂

namespace AffineIsometryEquiv

variable (e : P ≃ᵃⁱ[𝕜] P₂)

variable (𝕜 P)

variable {𝕜 P}

variable {α : Type*} [TopologicalSpace α]

section Constructions

variable (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁] [Nonempty s₂]

variable {s₁}

variable (s₁)

variable {s₁ s₂}

@[simp]
theorem coe_vaddConst (p : P) : ⇑(vaddConst 𝕜 p) = fun v => v +ᵥ p :=
  rfl

end Constructions
end AffineIsometryEquiv
end
