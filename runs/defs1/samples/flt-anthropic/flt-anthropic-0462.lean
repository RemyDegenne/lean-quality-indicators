namespace P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction Topology

open scoped ENNReal NNReal Pointwise

noncomputable section

namespace BruhatCellHaar

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => (HeightOneSpectrum.adicCompletion K v)

local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))

local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

local notation "Fˣ" => ((HeightOneSpectrum.adicCompletion K v)ˣ)

scoped instance secondCountable_units : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

scoped instance secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance locallyCompactSpace_localGL' : LocallyCompactSpace G := locallyCompactSpace_localGL K v

section Chart

attribute [local instance] LanglandsTunnell.TateLocal.localBorel LanglandsTunnell.TateLocal.borelSpace_localBorel
  AutomorphicForm.localGLBorel AutomorphicForm.borelSpace_localGLBorel

scoped instance borelSpace_units_local : BorelSpace Fˣ := borelSpace_units

local notation "Q" => (Coord K v)

local notation "P" => (Pgrp K v)

scoped instance secondCountable_lowerTri : SecondCountableTopology ↥(lowerTri : Subgroup G) :=
  TopologicalSpace.Subtype.secondCountableTopology ((lowerTri : Subgroup G) : Set G)

scoped instance secondCountable_unip : SecondCountableTopology ↥(unip : Subgroup G) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unip : Subgroup G) : Set G)

scoped instance borelSpace_lowerTri : BorelSpace ↥(lowerTri : Subgroup G) := Subtype.borelSpace _

scoped instance borelSpace_unip : BorelSpace ↥(unip : Subgroup G) := Subtype.borelSpace _

scoped instance borelSpace_P : BorelSpace P := Prod.borelSpace

scoped instance locallyCompactSpace_lowerTri : LocallyCompactSpace ↥(lowerTri : Subgroup G) :=
  isClosed_lowerTri.locallyCompactSpace

scoped instance locallyCompactSpace_unip : LocallyCompactSpace ↥(unip : Subgroup G) := isClosed_unip.locallyCompactSpace

def cellMap (q : Q) : G := lowerUnipotentGL2 q.2.2.2 * diagUnits2 q.2.2.1 q.2.1 * unipotentGL2 q.1

end Chart
end BruhatCellHaar
end
end P2MW.S_AutomorphicForm_exists_haar_localGL2_eq_smul_map_lowerUnipotentGL2_mul_diagUnits2_mul_unipotentGL2
