@[expose] public section

variable {M A B : Type*}

namespace Submonoid

variable [Monoid M] {a : M}

open MonoidHom

theorem mem_closure_singleton {x y : M} : y ∈ closure ({x} : Set M) ↔ ∃ n : ℕ, x ^ n = y := by
  rw [closure_singleton_eq, mem_mrange]; rfl

end Submonoid
end
