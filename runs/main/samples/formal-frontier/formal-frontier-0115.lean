@[expose] public section

noncomputable section

open MvPolynomial

namespace ProjectiveSpace

universe u v

variable (R : Type u) [CommSemiring R] [StrongRankCondition R]

theorem finrank_homogeneousSubmodule_fin (n d : ℕ) :
    Module.finrank R (homogeneousSubmodule (Fin (n + 1)) R d) =
      (n + d).choose d := by
  rw [finrank_homogeneousSubmodule, Nat.multichoose_eq, Fintype.card_fin]
  congr 1
  omega

end ProjectiveSpace
end
end
