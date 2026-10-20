public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

variable {R : Type u} {C : Type v} {D : Type w} {E : Type x}

variable [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

variable [AddCommMonoid E] [Module R E] [Coalgebra R E]

namespace Subcoalgebra

@[simp]
theorem map_bot (f : C →ₗc[R] D) : (⊥ : Subcoalgebra R C).map f = ⊥ := by
  ext d
  simp only [← mem_toSubmodule, map_toSubmodule, bot_toSubmodule, Submodule.map_bot]

end Subcoalgebra
end TauCeti
end
