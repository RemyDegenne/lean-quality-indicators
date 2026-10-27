@[expose] public section

namespace Fin

variable {α : Type*} [Preorder α]

variable [DecidableEq α]

section

variable (a b : α) (hab : a < b)

/-- This is the order isomorphism from `Fin 2` to a finset `{a, b}` when `a < b`. -/
noncomputable def orderIsoPair :
    Fin 2 ≃o ({a, b} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩]
    (strictMono_vecEmpty.vecCons hab) (fun ⟨x, hx⟩ ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)

end
end Fin
end
