@[expose] public section

open scoped WithZero

universe u v

namespace MvPolynomial

variable {σ : Type v}

section Order

variable {R : Type u} [CommSemiring R]

/-- The finite order of a nonzero polynomial, with the convention that zero maps to zero. -/
noncomputable def weightOneNatOrder (S : Set σ) (p : MvPolynomial σ R) : ℕ :=
  (weightOneOrder S p).toNat

end Order
end MvPolynomial
end
