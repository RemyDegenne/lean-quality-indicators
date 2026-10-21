namespace OAI

section

namespace ElementaryPositivity.SlopeArithmetic

variable {I : Type*} [Fintype I]

lemma mass_eq (c η : I → ℝ) (hc : ∀ i,0 < c i) (d : I → ℕ) :
    mass η d = slope c η d * mass c d := by
  by_cases hd : d=0
  · subst d; simp
  · exact (div_mul_cancel₀ _ (mass_pos c hc d hd).ne').symm

end ElementaryPositivity.SlopeArithmetic
end
end OAI
