namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional

attribute [-instance] IsDedekindDomain.HeightOneSpectrum.instAlgebraRatAdicCompletion IsDedekindDomain.HeightOneSpectrum.instModuleRatAdicCompletion

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section ASM_D2R_Body_VPSd_v1

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

p2m_open

open NumberField.AdelicLevel (diagOne)

open UnramifiedWhittaker (unipotent)

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace VPSdD2R

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

local notation "τ" => (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)) :
  Measure (HeightOneSpectrum.adicCompletion ℚ p)ˣ)

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance : (selfDualHaarAt ℚ p).IsAddHaarMeasure := SC1D2R.isAddHaarMeasure_sd p

scoped instance : BorelSpace (F)ˣ := RS22GodementRefoldKit.borelSpace_units

scoped instance : SecondCountableTopology (F)ˣ := Units.isEmbedding_val₀.secondCountableTopology

scoped instance : LocallyCompactSpace (F)ˣ := by
  refine (⟨Units.isEmbedding_val₀, ?_⟩ : Topology.IsOpenEmbedding (Units.val : (F)ˣ → F)).locallyCompactSpace
  have : Set.range (Units.val : (F)ˣ → F) = {x | x ≠ 0} := by
    ext x
    simp only [Set.mem_range, Set.mem_setOf_eq]
    exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx => ⟨Units.mk0 x hx, rfl⟩⟩
  rw [this]; exact isOpen_ne

scoped instance isHaar_tau : (τ).IsHaarMeasure := LanglandsTunnell.TateLocal.isHaarMeasure_comap_val_mulMeasure ℚ p (selfDualHaarAt ℚ p)

scoped instance : SecondCountableTopology G := SC1D2R.secondCountableTopology_localGL p

scoped instance : LocallyCompactSpace G := AutomorphicForm.locallyCompactSpace_localGL ℚ p

theorem esc_row0 (y : (F)ˣ) (g : G) : ((esc p y * g : G) : Mat) 0 = (g : Mat) 0 := by
  funext j
  simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, coe_esc, Matrix.diagonal]

end VPSdD2R
end
end ASM_D2R_Body_VPSd_v1
end P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional
