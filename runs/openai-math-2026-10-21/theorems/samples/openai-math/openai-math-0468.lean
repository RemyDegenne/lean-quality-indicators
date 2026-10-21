namespace OAI

namespace MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine

theorem le_sum_of_mem {n : Nat} {xs : List Nat} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · have hrest := ih hm
      simp only [List.sum_cons]
      omega

end MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine
end OAI
