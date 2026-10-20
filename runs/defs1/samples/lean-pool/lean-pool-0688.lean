universe v

public noncomputable section

open HahnSeries

namespace Berarducci

variable {K : Type v} [Field K]

/-- The remainder in the product-rule form of Berarducci, Lemma 7.7, for `b ^ (m + 1) * c`. -/
def powerRemainder (b c : SeriesWithOrdinalValueAboveOne K) (m : ℕ) (γ : ℝ) : Germ K :=
  germAt ((b.1 ^ (m + 1) * c.1 : Series K) : K⟦ℝ⟧) γ
    - (m + 1) • (germAt (b.1 : K⟦ℝ⟧) γ * toGerm (b.1 ^ m * c.1))
    - toGerm (b.1 ^ (m + 1)) * germAt (c.1 : K⟦ℝ⟧) γ

end Berarducci
end
