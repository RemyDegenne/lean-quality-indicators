public section

noncomputable section

open groupCohomology

namespace TauCeti

section Cocycle

variable {K L : Type*} [CommSemiring K] [CommRing L] [Algebra K L]
  (h : Nat.card (L ≃ₐ[K] L) = 2)

namespace TwoCocycle

@[simp]
theorem quadratic_one : quadratic h (1 : Kˣ) = 1 :=
  TwoCocycle.ext <| funext₂ fun σ τ ↦ by
    rcases eq_or_ne σ 1 with rfl | hσ
    · simp
    rcases eq_or_ne τ 1 with rfl | hτ
    · simp
    simp [quadratic_toFun_of_ne_one_of_ne_one h _ hσ hτ]

end TwoCocycle
end Cocycle
end TauCeti
end
end
