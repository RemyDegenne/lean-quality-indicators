open scoped Finset

@[expose] public section

open Set Function

universe u v w x

variable {α : Type u} {β : Type v}

namespace Finset

section Preimage

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β}
    (hs : Set.InjOn f (f ⁻¹' ↑s)) (ht : Set.InjOn f (f ⁻¹' ↑t)) :
    (preimage (s ∩ t) f fun _ hx₁ _ hx₂ =>
        hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
      preimage s f hs ∩ preimage t f ht :=
  Finset.coe_injective (by simp)

end Preimage
end Finset
end
