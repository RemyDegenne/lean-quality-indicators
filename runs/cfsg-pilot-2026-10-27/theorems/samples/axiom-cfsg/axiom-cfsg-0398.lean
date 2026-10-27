public noncomputable section

namespace CFSG.Wreathed

theorem modFourSign_cases (q : ℕ) : modFourSign q = 1 ∨ modFourSign q = -1 := by
  unfold modFourSign
  split <;> simp

end CFSG.Wreathed
end
