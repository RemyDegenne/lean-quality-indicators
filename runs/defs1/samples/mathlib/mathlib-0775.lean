@[expose] public section

noncomputable section

open Polynomial

open Finset

variable {M N G R S F : Type*}

variable [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]

section rootsOfUnity

variable {k l : ℕ}

section CommMonoid

variable [CommMonoid R] [CommMonoid S] [FunLike F R S]

/-- Restrict a monoid isomorphism to the nth roots of unity. -/
nonrec def MulEquiv.restrictRootsOfUnity (σ : R ≃* S) (n : ℕ) :
    rootsOfUnity n R ≃* rootsOfUnity n S where
  toFun := restrictRootsOfUnity σ n
  invFun := restrictRootsOfUnity σ.symm n
  left_inv ξ := by ext; exact σ.symm_apply_apply _
  right_inv ξ := by ext; exact σ.apply_symm_apply _
  map_mul' := (restrictRootsOfUnity _ n).map_mul

end CommMonoid
end rootsOfUnity
end
end
