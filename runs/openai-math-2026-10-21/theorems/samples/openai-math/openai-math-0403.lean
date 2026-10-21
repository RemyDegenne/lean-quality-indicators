namespace OAI

noncomputable section

open FourierTransform

namespace LipschitzHilbert

variable {κ : Type*} [Fintype κ]

theorem planarPolynomialLocalization_vertical (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorVerticalSlice (planarPolynomialLocalization b r q f) x=
      vectorPolynomialLocalization b r q (vectorVerticalSlice f x) := by
  ext y k
  simp only [vectorVerticalSlice_apply,planarPolynomialLocalization_apply,vectorPolynomialLocalization_apply]

end LipschitzHilbert
end
end OAI
