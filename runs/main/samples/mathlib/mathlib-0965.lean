@[expose] public section

open Subgroup

variable (N : Type*) (G : Type*) {H : Type*} [Group N] [Group G] [Group H]

@[inherit_doc]
notation:35 N " ⋊[" φ:35 "] " G:35 => SemidirectProduct N G φ

namespace SemidirectProduct

variable {N G}

variable {φ : G →* MulAut N}

section Map

variable {N₁ G₁ N₂ G₂ : Type*} [Group N₁] [Group G₁] [Group N₂] [Group G₂]
  {φ₁ : G₁ →* MulAut N₁} {φ₂ : G₂ →* MulAut N₂}
  (fn : N₁ →* N₂) (fg : G₁ →* G₂)
  (h : ∀ g : G₁, fn.comp (φ₁ g).toMonoidHom = (φ₂ (fg g)).toMonoidHom.comp fn)

@[simp]
theorem map_left (g : N₁ ⋊[φ₁] G₁) : (map fn fg h g).left = fn g.left := rfl

end Map
end SemidirectProduct
end
