public section

namespace TauCeti

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]

@[simp]
theorem isPrimitive_neg {v : M} : IsPrimitive (-v) ↔ IsPrimitive v :=
  ⟨fun h ↦ by simpa using h.neg, IsPrimitive.neg⟩

end TauCeti
end
