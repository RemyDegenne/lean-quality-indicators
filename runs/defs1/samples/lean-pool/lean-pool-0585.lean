universe v

open scoped NatOrdinal HahnSeries

open Berarducci HahnSeries

public noncomputable section

namespace Berarducci

variable {K : Type v} [Field K]

section Family

variable (w : ℕ → Series K) (c γ : ℕ → ℝ) (hγ : StrictMono γ)
  (hdisj : ∀ k, γ k ≤ γ (k + 1) + c (k + 1))

include hγ hdisj

/-- The terms in the sum along cutoffs form a summable family. -/
def placedTerms : SummableFamily ℝ K ℕ where
  toFun := placedTerm w c γ
  isPWO_iUnion_support' :=
    Set.IsPWO.iUnion_of_ordered (fun k ↦ support_placedTerm_isPWO w c γ k)
      fun j k hjk x hx y hy ↦ placedTerm_support_lt w c γ hγ hdisj hjk hx hy
  finite_co_support' x := by
    refine Set.Subsingleton.finite fun j hj k hk ↦ ?_
    by_contra hne
    rcases Ne.lt_or_gt hne with h | h
    · exact (placedTerm_support_lt w c γ hγ hdisj h hj hk).false
    · exact (placedTerm_support_lt w c γ hγ hdisj h hk hj).false

end Family
end Berarducci
end
