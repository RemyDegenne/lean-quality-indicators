namespace OAI

namespace ParityWL.Complexity

lemma listCell_tail {a : ℕ} (xs : List (Fin (a+3))) (n : ℕ) :
    listCell xs.tail n = listCell xs (n+1) := by cases xs <;> simp

end ParityWL.Complexity
end OAI
