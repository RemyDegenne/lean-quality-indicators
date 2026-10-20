public section

namespace TauCeti

open LieAlgebra LieModule

section CommRing

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] [LieAlgebra ℚ L] {h e f : L}

variable (he : IsNilpotent (ad K L e)) (hf : IsNilpotent (ad K L f))
  (hf' : IsNilpotent (ad K L (-f)))

lemma expAd_e_apply_h (t : IsSl2Triple h e f) : expAd e he h = h - 2 • e := by
  have h₂ : ⁅e, h⁆ = -(2 • e) := by rw [← lie_skew e h, t.lie_h_e_nsmul]
  rw [expAd_apply_of_lie_lie_eq_zero he (by rw [h₂]; simp), h₂]
  abel

end CommRing
end TauCeti
end
