@[expose] public section

namespace Int

@[simp]
theorem shiftRight_neg (m n : ℤ) : m >>> (-n) = m <<< n := by rw [← shiftLeft_neg, neg_neg]

end Int
end
