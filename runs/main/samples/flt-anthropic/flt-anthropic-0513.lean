namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective

set_option autoImplicit false

open scoped BigOperators

open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace HeisC4a

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

theorem Tlin_single (γ : MulAut (Heis δ d)) (v : HH δ → B) (y : HH δ) :
    Tlin δ d B ω γ v (Pi.single y 1) = schrod δ d B ω (γ (Heis.theta y)) v := by
  classical
  rw [Tlin_apply, Finset.sum_eq_single y]
  · rw [Pi.single_eq_same, one_smul]
  · intro x _ hx; rw [Pi.single_eq_of_ne hx, zero_smul]
  · intro hy; exact absurd (Finset.mem_univ y) hy

end HeisC4a
end P2MW.S_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_forall_schrod_eta_apply_eq_of_bijective
