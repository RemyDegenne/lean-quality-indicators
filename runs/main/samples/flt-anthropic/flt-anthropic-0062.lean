namespace P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self

attribute [-instance] ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 8000000

p2m_reactivate

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.ModularCurve AlgebraicCurve in
theorem solution
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (τ : modularFunctionFieldC K p ≃ₐ[K] modularFunctionFieldC K p)
    (hτ₁ : τ ⟨jqModC K, jqModC_mem K p⟩ = ⟨jqNModC K p, jqNModC_mem K p⟩)
    (hτ₂ : τ ⟨jqNModC K p, jqNModC_mem K p⟩ = ⟨jqModC K, jqModC_mem K p⟩)
    (ω : Ω[modularFunctionFieldC K p⁄K]) :
    (letI := AlgebraicCurve.algebraAlong (heckeAlphaC K p p)
     haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K p p)
     qExpansionDiffAlong (modularFunctionFieldC K p).val
      (traceDiff K (modularFunctionFieldC K p) (charLDegeneracyRoof K p p)
        (pullbackDiff (heckeBetaC K p p) ω)))
    = (p : K) • qExpand K p (qExpansionDiffAlong (modularFunctionFieldC K p).val ω)
      + ∑ b ∈ Finset.Ico 1 p, qTwist (ζ ^ b)
          (qExpansionDiffAlong ((modularFunctionFieldC K p).val.comp
            (τ : modularFunctionFieldC K p →ₐ[K] modularFunctionFieldC K p)) ω) :=
  ModularCurve.LevelHeckeDiff.main K p ζ hζ τ hτ₁ hτ₂ ω

end P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self
