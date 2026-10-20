public section

noncomputable section

open QuadraticAlgebra

namespace QuadraticAlgebra

theorem classGroup_eq_one_or_mk0_sqrtNegFiveRingOfIntegersIdealTwo
    (C : ClassGroup SqrtNegFiveRingOfIntegers) :
    C = 1 ∨ C = ClassGroup.mk0 sqrtNegFiveRingOfIntegersIdealTwoNonzero := by
  obtain ⟨I, hclass, hnorm⟩ :=
    exists_ideal_in_class_of_absNorm_le_two C
  rcases
      eq_top_or_eq_sqrtNegFiveRingOfIntegersIdealTwo_of_absNorm_le_two I hnorm with
    htop | htwo
  · left
    rw [← hclass]
    exact (ClassGroup.mk0_eq_one_iff I.prop).mpr
      (htop.symm ▸ top_isPrincipal)
  · right
    rw [← hclass]
    congr 1
    exact Subtype.ext htwo

end QuadraticAlgebra
end
end
