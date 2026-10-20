public section

open Polynomial

namespace Finset

variable {n : ℕ}

@[simp]
theorem integerProjection_empty :
    (∅ : Finset (MvPolynomial (Fin (n + 1)) ℤ)).integerProjection = ∅ := by
  simp [integerProjection_def]

end Finset
end
