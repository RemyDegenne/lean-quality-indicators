@[expose] public noncomputable section

open Module

section StrictOrderedCommSemiring

variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (R M)

/-- A ray (equivalence class of nonzero vectors with common positive multiples) in a module. -/
def Module.Ray :=
  Quotient (RayVector.Setoid R M)

end StrictOrderedCommSemiring
end
