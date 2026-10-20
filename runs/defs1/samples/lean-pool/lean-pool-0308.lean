@[expose] public section

namespace UnrestrictedBooleanMul

noncomputable section

/-- A squarefree monomial in `m` Boolean variables. -/
@[ext]
structure Monomial (m : Nat) where
  /-- Variables occurring in this squarefree monomial. -/
  vars : Finset (Fin m)

end
end UnrestrictedBooleanMul
end
