universe v w

open scoped HahnSeries

public noncomputable section

namespace Berarducci.OneRow

variable {K : Type v} [Field K]

/-- The coefficient-one nonpositive Hahn series `Σ n, t ^ (-1 / (n + 1))`. -/
def withoutConstant : Series K :=
  ⟨HahnSeries.embDomain exponentEmbedding (coefficientOne (K := K)), by
    rw [HahnSeries.mem_nonpositiveSubring,
      HahnSeries.support_embDomain, coefficientOne_support, Set.image_univ]
    rintro _ ⟨n, rfl⟩
    rw [exponentEmbedding_apply, exponent_apply]
    exact neg_nonpos.mpr (show 0 ≤ 1 / (n + 1 : ℝ) by positivity)⟩

end Berarducci.OneRow
end
