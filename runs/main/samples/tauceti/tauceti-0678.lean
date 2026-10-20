public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

section BoundedFlow

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K]

namespace BoundedFlow

section Preorder

variable [Preorder K] {lo hi : Assignment Q K} {s t : V}

@[simp]
theorem swap_swap (f : BoundedFlow lo hi s t) : f.swap.swap = f :=
  (rfl)

end Preorder
end BoundedFlow
end BoundedFlow
end TauCeti
end
