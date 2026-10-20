@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

open Set

universe u v w

namespace TopologicalSpace.IrreducibleCloseds

variable {X : Type u} {Y : Type v} {Z : Type w}

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem isClosed_iff (D : Set (IrreducibleCloseds X)) :
    IsClosed D ↔ ∃ Z : Set X, IsClosed Z ∧ D = closedSet Z := by
  constructor
  · intro hD
    obtain ⟨U, hU⟩ := (isOpen_iff Dᶜ).mp hD.isOpen_compl
    refine ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, ?_⟩
    apply compl_injective
    rw [hU, compl_closedSet U.isOpen.isClosed_compl]
    ext F
    change ((F : Set X) ∩ (U : Set X)).Nonempty ↔
      ((F : Set X) ∩ (((U : Set X)ᶜ)ᶜ)).Nonempty
    simp only [compl_compl]
  · rintro ⟨Z, hZ, rfl⟩
    exact isClosed_closedSet hZ

end TopologicalSpace.IrreducibleCloseds
end
