public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Linear

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem ringEquiv_eq_one_of_card_two (hK : Nat.card K = 2) (τ : K ≃+* K) : τ = 1 := by
  have hsub : Subsingleton Kˣ := by
    have h : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    exact (Nat.card_eq_one_iff_unique.mp h).1
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · have h1 : x = 1 := by
      have := Subsingleton.elim (Units.mk0 x hx) 1
      exact congrArg (fun u : Kˣ => (u : K)) this
    simp [h1]

end Linear
end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
end
