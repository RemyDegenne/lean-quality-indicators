namespace P2MW.S_AutomorphicForm_setIntegral_convOp_residualProjection_eq_mul_setIntegral_prod_finsum_chiDet_mul_chiDet_inv

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open IsDedekindDomain

open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace ResRect19

noncomputable section

open AutomorphicForm Filter

variable (K : Type) [Field K] [NumberField K]

section Aut

variable (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
  (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)

local notation "μH" => adelicGLHaar (Fin 2) (𝓞 K) K

local notation "Φ₀" => canonicalTruncationDomain K α β

local notation "PINS" => productionPinsOf K (canonicalTruncationDomain K α β)
    (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

include hα hαβ in

theorem aesm_of_aut (hdat : ∃ d, IsTruncationDatum K α β d) {h : AdelicGL2 (𝓞 K) K → ℂ}
    (hh : IsAutomorphicFnAt K PINS ξK h) : AEStronglyMeasurable h μH := by
  obtain ⟨-, -, -, hsub, hFD⟩ := canonicalTruncationData_spec K hdat
  exact AutomorphicForm.aestronglyMeasurable_adelicGLHaar_of_isAutomorphicFnAt_slab K α β hα hαβ Φ₀ hsub hFD ξK h hh

end Aut
end
end ResRect19
end P2MW.S_AutomorphicForm_setIntegral_convOp_residualProjection_eq_mul_setIntegral_prod_finsum_chiDet_mul_chiDet_inv
