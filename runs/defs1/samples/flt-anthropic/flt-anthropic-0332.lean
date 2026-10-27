namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint

attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace LBShared

open IsLocalRing NeronSpecialFibreInfra ModularCurve ModularCurve.JZeroNeronObjectAtP

variable {A : ValuationSubring (AlgebraicClosure ℚ)} {t : ℕ}

abbrev red {t : ℕ} (ℓ : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod ℓ) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod ℓ)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

end LBShared
end
end P2MW.S_ModularCurve_JZeroNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_forall_prime_pow_smul_toricPoint
