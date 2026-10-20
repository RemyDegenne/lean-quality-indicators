namespace P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two

open scoped TensorProduct

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

namespace P2mTwoPointHopf

noncomputable section

p2m_reactivate

p2m_reactivate

section CaseA

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

attribute [local instance] isScalarTower_int

attribute [local instance] instHopfP2

theorem comul_P2_e (g : Fin 2) :
    Bialgebra.comulAlgHom ℤ P2 (Const.e ℤ (Fin 2) g) =
      Const.e ℤ (Fin 2) 0 ⊗ₜ[ℤ] Const.e ℤ (Fin 2) g + Const.e ℤ (Fin 2) 1 ⊗ₜ[ℤ] Const.e ℤ (Fin 2) (g - 1) := by
  rw [comul_P2, Const.comulLin_e, Fin.sum_univ_two, sub_zero]

end CaseA
end
end P2mTwoPointHopf
end P2MW.S_HopfAlgebra_prime_and_exists_isLocalizationAway_of_not_module_finite_of_natCard_algHom_eq_two
