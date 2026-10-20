namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight

attribute [-instance] instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE

attribute [-instance] LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open IsDedekindDomain

open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField.TateGlobal AutomorphicForm

noncomputable section

open Complex

open Complex

open NumberField IsDedekindDomain AutomorphicForm

open NumberField.TateGlobal

open scoped Classical

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel

open NumberField.TateGlobal

open scoped Classical

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel

open NumberField.TateGlobal

open scoped Classical

namespace Ws31

namespace C3Glue

p2m_open

variable {K : Type} [Field K] [NumberField K]

theorem ideleNorm_archUnitHom'' (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ideleNorm K (archUnitHom w x) = ‖(x : w.Completion)‖ ^ w.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archUnitHom w x) rfl,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ w)]
  have h1 : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)).erase w,
      ‖((archUnitHom w x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v‖ ^ v.mult = 1 := by
    intro v hv
    have hvw : v ≠ w := Finset.ne_of_mem_erase hv
    show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) v‖ ^ v.mult = 1
    rw [Function.update_of_ne hvw]
    change ‖(1 : v.Completion)‖ ^ v.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one h1, one_mul]
  show ‖Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion) w‖ ^ w.mult = _
  rw [Function.update_self]

end C3Glue
end Ws31
end
end P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight
