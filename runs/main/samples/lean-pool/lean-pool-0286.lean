universe v

public noncomputable section

namespace Berarducci

open scoped DirectSum HahnSeries NatOrdinal

variable {K : Type v} [Field K]

variable (K) in
theorem principalComponentToHahnDegreeLayer_componentOne :
    principalComponentToHahnDegreeLayer K 0
        (ordinalValueDegreeValuation K).componentOne =
      (HahnSeries.Nonpositive.degreeValuation K).componentOne := by
  let wOrder := ordinalValueDegreeValuation K
  let wDegree := HahnSeries.Nonpositive.degreeValuation K
  let e := principalDegreeClassesEquivPrincipalComponent K 0
  have honeDegree : (((1 : Series K) : K⟦ℝ⟧)).degree =
      (0 : WithBot NatOrdinal) := by
    rw [← map_one (HahnSeries.Nonpositive.C : K →+* Series K)]
    exact degree_C_eq_zero_of_ne one_ne_zero
  have honeClass : wDegree.componentOne ∈ principalDegreeClasses K 0 := by
    rw [mem_principalDegreeClasses_iff, isPrincipalDegreeClass_iff]
    refine Or.inr ⟨1, HahnSeries.Nonpositive.isPrincipal_one, honeDegree, ?_⟩
    rw [wDegree.componentOne_eq_componentMk, degreeLayerMk_eq_componentMk]
  change ((e.symm wOrder.componentOne : principalDegreeClasses K 0) :
      wDegree.Component 0) = wDegree.componentOne
  have heq : e.symm wOrder.componentOne = ⟨wDegree.componentOne, honeClass⟩ := by
    apply e.injective
    rw [e.apply_symm_apply,
      principalDegreeClassesEquivPrincipalComponent_apply,
      degreeLayerToPrincipalComponent_eq_componentMap]
    exact (MaxAddDegree.componentMap_componentOne _ _ _ _).symm
  exact congrArg Subtype.val heq

end Berarducci
end
