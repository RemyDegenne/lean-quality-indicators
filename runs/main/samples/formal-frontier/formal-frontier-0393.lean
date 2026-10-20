@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace Module

variable (R : Type u) [CommRing R]

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

namespace DeterminantLine

@[simp]
theorem component_zero (i : rankFiberIndex R P) :
    component R P i (0 : DeterminantLine R P) = 0 :=
  rfl

end DeterminantLine
end Module
end
end
