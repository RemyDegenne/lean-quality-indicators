public section

namespace WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

section ShortNF

variable (C : VariableChange R) [W.IsShortNF] [(C • W).IsShortNF]

include W

lemma VariableChange.r_eq_zero_of_isShortNF (h2 : IsRegular (2 : R)) (h3 : IsRegular (3 : R)) :
    C.r = 0 := by
  have h := (C • W).a₂_of_isShortNF
  rw [variableChange_a₂, W.a₁_of_isShortNF, W.a₂_of_isShortNF, C.s_eq_zero_of_isShortNF W h2,
    (C.u⁻¹.isUnit.pow 2).mul_right_eq_zero] at h
  exact h3.left (by simp only [mul_zero]; linear_combination h)

end ShortNF
end WeierstrassCurve
end
