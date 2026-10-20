namespace P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two

open scoped TensorProduct

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace P2mTwoPointHopf

noncomputable section

section TateOort

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

variable {K}

variable (T : TOData K)

theorem TOData.χ₀_eq (k : K) : T.χ₀ k = (Bialgebra.counitAlgHom ℤ K k : ℚ) + T.a * T.lam0 k := by
  change T.χQ (toKQ K k) = _
  rw [T.χQ_apply, counit_toKQ]
  rfl

end TateOort
end
end P2mTwoPointHopf
end P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
