public section

namespace Tests

theorem nat_zero_right_refinement (b c : ℕ) :
    ∃ e f g h : ℕ, 0 = e * f ∧ b = g * h ∧ c = e * g ∧ 0 = f * h :=
  nat_hasFourFactorRefinement.refine (by simp)

end Tests
end
