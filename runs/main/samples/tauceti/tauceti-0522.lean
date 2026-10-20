public section

namespace TauCeti

open Topology

universe u v

variable (R : Type u) [CommRing R] (Γ : Type v) [Group Γ] [TopologicalSpace Γ]

namespace completedGroupAlgebra

variable {R Γ}

variable (R Γ)

section UniformSpace

variable [UniformSpace R]

theorem isUniformEmbedding_coeffFamily : IsUniformEmbedding (coeffFamily R Γ) :=
  ⟨isUniformInducing_coeffFamily R Γ, coeffFamily_injective R Γ⟩

end UniformSpace
end completedGroupAlgebra
end TauCeti
end
