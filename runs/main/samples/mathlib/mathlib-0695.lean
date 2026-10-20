@[expose] public section

variable {R M M₂ V S : Type*}

namespace Submodule

open Function Set

open scoped Pointwise

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {x : M} (p p' : Submodule R M)

variable [AddCommMonoid M₂]

variable {s t : Set M}

notation:70 R:70 " ∙ " x:70 => span R (singleton x)

section

variable {p p'}

variable (p p')

theorem coe_sup : ↑(p ⊔ p') = (p + p' : Set M) := by
  ext
  rw [SetLike.mem_coe, mem_sup, Set.mem_add]
  simp

end
end AddCommMonoid
end Submodule
end
