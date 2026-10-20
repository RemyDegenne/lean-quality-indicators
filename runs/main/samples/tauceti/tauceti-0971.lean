public section

open Function

namespace TauCeti

section Coboundary

section NonAssoc

variable (R A M : Type*) [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

variable {R A M} {n : ℕ}

@[simp]
theorem hochschildCoboundary_apply (φ : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M)
    (a : Fin (n + 2) → A) :
    hochschildCoboundary R A M n φ a =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • φ (hochschildFace i a) := by
  simp [hochschildCoboundary]

end NonAssoc
end Coboundary
end TauCeti
end
