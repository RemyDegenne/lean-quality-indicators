public section

namespace WeierstrassCurve

open IsLocalRing Polynomial TauCeti

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ϖ : R)

variable {W ϖ}

@[simp]
theorem tateLocalIndex_I_add_one_of_not_hasTateTangentRoot (h : ¬ W.HasTateTangentRoot ϖ)
    (n : ℕ) : W.tateLocalIndex ϖ (.I (n + 1)) = Nat.gcd 2 (n + 1) := by
  simp [tateLocalIndex, h]

end CommRing
end WeierstrassCurve
end
