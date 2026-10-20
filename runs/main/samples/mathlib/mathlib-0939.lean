@[expose] public section

noncomputable section

open Polynomial Finset

variable {M N G R S F : Type*} [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]

namespace IsPrimitiveRoot

variable {k l : ℕ}

section IsDomain

variable [CommRing R] {ζ : Rˣ} (h : IsPrimitiveRoot ζ k)

variable [IsDomain R]

theorem card_nthRoots_one {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    Multiset.card (nthRoots n (1 : R)) = n := by
  rw [card_nthRoots h, ite_eq_left ⟨ζ, h.pow_eq_one⟩]

end IsDomain
end IsPrimitiveRoot
end
end
