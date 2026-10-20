@[expose] public section

universe u

variable (R₀ R : Type*) (M : Type u) (N S : Type*) [CommSemiring R₀]
  [Ring R] [Algebra R₀ R] [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup S] [Module R M] [Module R N] [Module R S]

variable {R}

variable {M N S}

variable (R M S)

variable {R M}

variable [IsSemisimpleModule R M]

open IsSemisimpleModule

theorem isFullyInvariant_iff_sSup_isotypicComponents {m : Submodule R M} :
    m.IsFullyInvariant ↔ ∃ s ⊆ isotypicComponents R M, m = sSup s := by
  refine ⟨fun h ↦ ⟨OrderIso.setIsotypicComponents.symm ⟨m, h⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rintro _ ⟨c, _, rfl⟩; exact c.2
  · convert Subtype.ext_iff.mp (OrderIso.setIsotypicComponents.right_inv ⟨m, h⟩).symm
    simp [sSup_image, OrderIso.setIsotypicComponents, OrderIso.symm]
  · rintro ⟨_, hs, rfl⟩
    exact (fullyInvariantSubmodule R M).sSupClosed fun _ h ↦ .of_mem_isotypicComponents (hs h)

end
