namespace P2MW.S_UnipotentTermUnfolding_forall_exists_lintegral_iwasawa_tsum_tsum_enorm_sub_ne_top_of_isSemiLocalFactorization

attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

open MeasureTheory NumberField

open scoped Pointwise ENNReal

noncomputable section

namespace R1FibreUnfold

section Measurability

open AutomorphicForm AutomorphicForm.TwistedBruhat NumberField.AdelicHeight IsDedekindDomain

open NumberField.AdelicHaar NumberField.AdelicBox

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

attribute [local instance] borelSpace_adele

theorem measurable_fibreTerm
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (hloc : AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (s : Lˣ) (a : N1 K L) :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => fibreTerm K L D σ hgen φ R p.1 p.2 s a := by
  classical
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_units_adeleRing L
  simp only [fibreTerm_eq]
  set T' : Set (GL (Fin 2) L) := normUnipotentSet K L σ hgen ∩ fib L (s : L) ((s : L) * ((a : Lˣ) : L))
  set T'' : Set (GL (Fin 2) L) := fib L (s : L) ((s : L) * ((a : Lˣ) : L))
  have hKm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      Bf K L D σ T' φ p.1 (centralScalar (𝓞 L) L p.2 * p.1) :=
    (continuous_Bf K L D σ hloc φ hφc hφs T').measurable
  have hhigh : MeasurableSet {p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ |
      Real.exp R < adelicHeight L (centralScalar (𝓞 L) L p.2 * p.1)} :=
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst)).measurable measurableSet_Ioi
  have hCT : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∫ q, (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
        Bf K L D σ T'' φ r.1.1 (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1))) (p, q)
        ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    (continuous_Bf_unipotent K L D σ hloc φ hφc hφs T'').stronglyMeasurable.integral_prod_right'
  have hTm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      Set.indicator (highSet (adelicHeight L) (Real.exp R)) (CTf K L D σ T'' φ p.1)
        (centralScalar (𝓞 L) L p.2 * p.1) := by
    simp_rw [indicator_CTf_eq_ite]
    exact Measurable.ite hhigh hCT.measurable measurable_const
  exact hKm.sub hTm

end Measurability
end R1FibreUnfold
end
end P2MW.S_UnipotentTermUnfolding_forall_exists_lintegral_iwasawa_tsum_tsum_enorm_sub_ne_top_of_isSemiLocalFactorization
