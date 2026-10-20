@[expose] public section

universe u v w

noncomputable section

open scoped Topology ENNReal NNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight toSpanSingleton_inj toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f f₀ f₁ : 𝕜 → F}

variable {f' f₀' f₁' g' : F}

variable {x : 𝕜}

variable {s t : Set 𝕜}

variable {L L₁ L₂ : Filter (𝕜 × 𝕜)}

section congr

theorem HasStrictDerivAt.congr_deriv (h : HasStrictDerivAt f f' x) (h' : f' = g') :
    HasStrictDerivAt f g' x :=
  h.hasStrictFDerivAt.congr_fderiv <| congr_arg _ h'

end congr
end
end
