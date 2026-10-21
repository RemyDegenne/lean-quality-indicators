namespace OAI

namespace TwoPointCorrelations

open Finset

open scoped Classical

lemma actualPaddingBin_sum_le (bins : Finset ℤ) (η c : ℝ) (hη : 0 < η)
    (q : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (∑ j ∈ bins, if actualPaddingBin η c j q then w else 0) ≤ w := by
  have he (j : ℤ) : actualPaddingBin η c j q ↔ paddingBin η c (Real.log q) = j :=
    (paddingBin_eq_iff η c (Real.log q) j hη).symm
  simp only [he]
  by_cases hm : paddingBin η c (Real.log q) ∈ bins
  · simp [hm]
  · simpa [hm] using hw

end TwoPointCorrelations
end OAI
