@[expose] public section

namespace Int

lemma negOnePow_sub (n₁ n₂ : ℤ) :
    (n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negOnePow := by
  simp only [sub_eq_add_neg, negOnePow_add, negOnePow_neg]

end Int
end
