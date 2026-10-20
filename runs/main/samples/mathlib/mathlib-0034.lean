set_option linter.style.longFile 1700

@[expose] public section

universe u v w x

open Module

open scoped Pointwise

namespace Ideal

section Semiring

variable {R : Type u} [Semiring R] {I J K L : Ideal R}

variable (I)

variable {I}

variable (I J K)

variable {I J K}

theorem pow_eq_bot [IsReduced R] {n : ℕ} (hn : n ≠ 0) : I ^ n = ⊥ ↔ I = ⊥ :=
  Submodule.pow_eq_bot hn

end Semiring
end Ideal
end
