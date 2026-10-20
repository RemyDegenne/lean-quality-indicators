public section

namespace TauCeti

lemma product_apply_stdComplexLineConj (z : ℝ × ℝ) :
    AlmostComplexStructure.product ℝ (stdComplexLineConj z) =
      -stdComplexLineConj (AlmostComplexStructure.product ℝ z) := by
  rw [stdComplexLineConj_apply_product]
  simp

end TauCeti
end
