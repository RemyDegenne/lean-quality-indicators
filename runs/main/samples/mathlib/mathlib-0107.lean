@[expose] public section

universe u v w w₁ w₂

section LieSubalgebra

open Set

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {R L}

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

namespace LieSubalgebra

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

section LieSpan

variable (R L) (s : Set L)

variable {R L s}

theorem submodule_span_le_lieSpan : Submodule.span R s ≤ lieSpan R L s := by
  rw [Submodule.span_le, coe_toSubmodule]
  apply subset_lieSpan

end LieSpan
end LieSubalgebra
end LieSubalgebra
end
