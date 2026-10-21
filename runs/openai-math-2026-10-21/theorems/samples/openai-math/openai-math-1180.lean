namespace OAI

namespace ContingencyTables.ForestIntegerEvaluation

open CompanionFactorialApplication CompanionOracleDensity ForestAffineCoefficients

open ForestAssignmentSplit GraphCompletionCounts

open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma offset_cast (A : Instance I J) (t : TreeCell A.T) (x q : I → J → ℤ) :
    (offset A t x q:ℚ)=rationalOffset A t x q := by
  have hs := selfSign_square A t
  have hn : rationalSign A t t.val≠0 := by intro h; rw [h] at hs; norm_num at hs
  have he : rationalSmallContribution A t x q*rationalSign A t t.val=
      rationalSmallContribution A t x q/rationalSign A t t.val := by
    apply (eq_div_iff hn).mpr
    rw [mul_assoc,←pow_two,hs,mul_one]
  simp only [offset,rationalOffset,Int.cast_sub,Int.cast_mul,Int.cast_sum,
    smallContribution_cast,sign_cast,coefficient_cast,he]

end
end ContingencyTables.ForestIntegerEvaluation
end OAI
