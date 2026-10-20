public section

open scoped InnerProductSpace

open TauCeti

namespace ContRepresentation

section Monoid

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Monoid G]
  [TopologicalSpace G] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

@[simp]
theorem character_restrict {H : Type*} [Monoid H] [TopologicalSpace H] (φ : H →* G)
    (hφ : Continuous φ) :
    character (π.restrict φ) (hπ.comp hφ) = (character π hπ).comp ⟨φ, hφ⟩ := by
  ext h
  rw [character_apply, ContinuousMap.comp_apply, character_apply, ContinuousMap.coe_mk,
    ContRepresentation.restrict_apply]

end Monoid
end ContRepresentation
end
