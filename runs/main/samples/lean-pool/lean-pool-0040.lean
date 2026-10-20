@[expose] public section

namespace BGS.Markoff

open Polynomial AdjoinRoot

noncomputable section

section RationalBase

variable {K : Type*} [Field K]

lemma norm_splitTraceBaseRoot
    (sigma : K) (hsigma : sigma ≠ 0) :
    letI : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) :=
      ⟨splitTraceBaseKummerPolynomial_irreducible sigma hsigma⟩
    Algebra.norm (RatFunc K)
      (AdjoinRoot.root (splitTraceBaseKummerPolynomial sigma)) =
        -splitTraceRadicand sigma := by
  let hIrred := splitTraceBaseKummerPolynomial_irreducible sigma hsigma
  let : Fact (Irreducible (splitTraceBaseKummerPolynomial sigma)) := ⟨hIrred⟩
  let pb := AdjoinRoot.powerBasis hIrred.ne_zero
  have hdim : pb.dim = 2 := by
    change (splitTraceBaseKummerPolynomial sigma).natDegree = 2
    simp [splitTraceBaseKummerPolynomial]
  change Algebra.norm (RatFunc K) pb.gen = -splitTraceRadicand sigma
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim,
    AdjoinRoot.minpoly_powerBasis_gen_of_monic]
  · simp [ splitTraceBaseKummerPolynomial]
  · exact monic_X_pow_sub_C _ (by norm_num)

end RationalBase
end
end BGS.Markoff
end
