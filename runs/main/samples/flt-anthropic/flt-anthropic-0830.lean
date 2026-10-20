namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion

section ASM_Blocks_SC1D2R

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

p2m_open

open NumberField.AdelicLevel (diagOne)

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace SC1D2R

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "ψ" => (NumberField.StandardAddChar.psiLocal ℚ p)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance locallyCompactSpace_unip : LocallyCompactSpace (unip p) := (isClosed_unip p).locallyCompactSpace

scoped instance secondCountable_unip : SecondCountableTopology (unip p) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip p : Subgroup G) : Set G)

theorem det_conj (w₀p : G) (hw₀p : (w₀p : Mat) = !![0, 1; 1, 0]) (g : G) :
    Matrix.GeneralLinearGroup.det (diagonal2 p ![1, -1] * g * w₀p) = Matrix.GeneralLinearGroup.det g := by
  rw [map_mul, map_mul]
  have h1 : Matrix.GeneralLinearGroup.det (diagonal2 p ![1, -1] : G) = -1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, WflatD2R.coe_diag', Matrix.det_fin_two_of]
    simp
  have h2 : Matrix.GeneralLinearGroup.det w₀p = -1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, hw₀p, Matrix.det_fin_two_of]
    simp
  rw [h1, h2, mul_comm (-1 : (F)ˣ), mul_assoc, neg_one_mul, neg_neg, mul_one]

end Main
end SC1D2R
end
end ASM_Blocks_SC1D2R
end P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional
