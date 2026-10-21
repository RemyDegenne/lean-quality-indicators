namespace OAI

universe uI uI2 uA uD uI3 uD2

section

namespace StrongThinTree.MSS

noncomputable section

open Finset Polynomial

open scoped Classical ComplexOrder

variable {I : Type uI2} [DecidableEq I]

lemma inverse_difference_im_neg {z a : ℂ} (hz : 0 < z.im) (ha : a.im ≤ 0) :
    (1/(z-a)).im < 0 := by
  have hd : 0 < (z-a).im := by simp only [Complex.sub_im]; linarith
  have hd0 : z-a ≠ 0 := fun h => by simpa [h] using hd.ne'
  simp only [one_div,Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hd) (Complex.normSq_pos.mpr hd0)

end
end StrongThinTree.MSS
end
end OAI
