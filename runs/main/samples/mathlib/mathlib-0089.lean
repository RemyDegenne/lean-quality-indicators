@[expose] public section

namespace LieModule.Cohomology

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

lemma mem_twoCocycle_iff (a : twoCochain R L M) : a ∈ twoCocycle R L M ↔ d₂₃ R L M a = 0 := by
  simp [twoCocycle]

end LieModule.Cohomology
end
