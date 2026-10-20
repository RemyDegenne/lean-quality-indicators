@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set TopologicalSpace

open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

theorem spectralSpace_sInter_of_compactOpenCofinal [SpectralSpace X]
    (F : Set (Set X))
    (hF : ∀ U ∈ F, ∃ V ∈ F, IsOpen V ∧ IsCompact V ∧ V ⊆ U) :
    SpectralSpace (⋂₀ F) :=
  spectralSpace_subtype_of_isClosed_constructible
    (isClosed_constructible_sInter_of_compactOpenCofinal F hF)

end
