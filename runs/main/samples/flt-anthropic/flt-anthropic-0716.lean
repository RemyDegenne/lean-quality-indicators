namespace P2MW.S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence

attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

p2m_open

namespace AlgebraicCurve

namespace PlaceReductionCorrespondence

p2m_open

section Fibre

variable {K F E FE F' F'E : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
  [IsCurveOver K F]
  [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
  [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
  [Field F'] [Algebra K F'] [IsCurveOver K F']
  [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
  [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]

omit [IsAlgClosed E] [IsCurveOver E FE] in

theorem fibre_identity_of_not_forall_mem
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    {P : Place E FE} (hint : ¬ ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring)
    {q : Place K F'} (hq : q ∈ Place.fiberAlong φ hφ (r P)) [DecidableEq (Place K F')] :
    ∑ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q),
        (W.ramificationIndexAlong φE : ℤ) = q.ramificationIndexAlong φ := by

  have hrP : (r P).toValuationSubring = P.toValuationSubring.comap (algebraMap F FE) :=
    reduction_eq_comap_of_not_forall_mem hfg A hKA r hr hint
  obtain ⟨P', -, hP'ord, hP'u⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE hgen (r P)
  have hPP' : P = P' := hP'u P hrP.symm
  have hPord : ∀ f : F, P.ord (algebraMap F FE f) = (r P).ord f := fun f => by
    rw [← hP'ord f, hPP']

  obtain ⟨Wq, hWq, hWqord, hWqu⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F' E F'E hfg' hfgE' hgen' q
  have hqv : q.restrictAlong φ hφ = r P := Place.mem_fiberAlong.mp hq

  have hWqP : Wq.restrictAlong φE hφE = P := by
    rw [hPP']
    refine hP'u _ (SetLike.ext fun f => ?_)
    rw [ValuationSubring.mem_comap, mem_restrictAlong_iff, hφcomm, ← hqv, mem_restrictAlong_iff,
      ← hWq, ValuationSubring.mem_comap]

  have hrWq : r' Wq = q := by
    refine Place.ext (SetLike.ext fun g => ?_)
    rw [hr', exists_mem_valuation_sub_lt_one_iff_of_comap Wq q hWq.symm A hKA g, ← hWq,
      ValuationSubring.mem_comap]

  obtain ⟨f₀, hf₀⟩ : ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring := by
    push Not at hint
    exact hint
  have huniq : ∀ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q), W = Wq := by
    intro W hW
    obtain ⟨hWZ, hWq'⟩ := Finset.mem_filter.mp hW
    have hWP : W.restrictAlong φE hφE = P := Place.mem_fiberAlong.mp hWZ

    have hWint : ¬ ∀ g : F', algebraMap F' F'E g ∈ W.toValuationSubring := fun h => hf₀ (by
      rw [← hWP, mem_restrictAlong_iff, hφcomm]
      exact h (φ f₀))
    have hW' : (r' W).toValuationSubring = W.toValuationSubring.comap (algebraMap F' F'E) :=
      reduction_eq_comap_of_not_forall_mem hfg' A hKA r' hr' hWint
    rw [hWq'] at hW'
    exact hWqu W hW'.symm

  have he : Wq.ramificationIndexAlong φE = q.ramificationIndexAlong φ :=
    ramificationIndexAlong_eq_of_ord_eq φ hφ φE hφE hφcomm hPord hqv hWqord hWqP

  have hmem : Wq ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q) :=
    Finset.mem_filter.mpr ⟨Place.mem_fiberAlong.mpr hWqP, hrWq⟩
  have hsingle : (Place.fiberAlong φE hφE P).filter (fun W => r' W = q) = {Wq} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, huniq⟩
  rw [hsingle, Finset.sum_singleton, he]

end Fibre
end PlaceReductionCorrespondence
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence
