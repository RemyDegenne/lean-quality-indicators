namespace P2MW.S_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo

attribute [-instance] instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure

set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

set_option Elab.async false

p2m_open

noncomputable section

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open

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

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_open "ModularCurve~coeffEmb_jq" in open Ws23.SlopeLawW _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.AlgebraicCurve IsLocalRing _root_.P2MW.S_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne.ModularCurve in

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ)
    [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hp5 : 5 ≤ p)
    {Fbar0 : Type}
    [Field Fbar0]
    [Algebra (IsLocalRing.ResidueField ↥A) Fbar0]
    (C0 : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) Fbar0)
    (x0 : Place (IsLocalRing.ResidueField ↥A) Fbar0)
    (a : IsLocalRing.ResidueField ↥A)
    (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A))
    (ha2 : a ^ (p ^ 2) = a)
    (hw : a = 0 ∨ a = 1728)
    (hnodes0 : x0 ∈ C0.nodes)
    (An : Annulus A ↥(modularFunctionFieldBar (1 * p)))
    (z : ↥(modularFunctionFieldBar (1 * p)))
    (hz : An.param = z)
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)), W ∈ An.dom ↔
          ((∃ x : A, IsLocalRing.residue ↥A x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩ : modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (x : AlgebraicClosure ℚ))) ∧
           (∃ y : A, IsLocalRing.residue ↥A y = a ^ p ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * p) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_refl (1 * p)))⟩ :
                modularFunctionFieldBar (1 * p))
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (y : AlgebraicClosure ℚ)))))
    (hzg : ∃ (h : ((frickeInvolutionBar (1 * p) z : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (z' : ↥(modularFunctionFieldBar (1 * p)))
    (hmod : z' * z = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (((p : ℕ) : AlgebraicClosure ℚ) ^ jWidth a))
    (hzg' : ∃ (h : ((z' : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
         (hF : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
         CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h⟩ ≠ 0 ∧
         (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) a).ord (⟨_, hF⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) = 1)
    (hunit0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p)))
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A)),
        CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ≠ 0 →
        ∃ hg : g ∈ C0.integers, C0.residue ⟨g, hg⟩ ≠ 0)
    (hordres0 : ∀ (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ C0.integers)
        (h₂ : ((frickeInvolutionBar (1 * p) g : modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
            CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A))
        (h₂F : CharPReduction.modularRedLocHom (1 * p) A.toSubring (IsLocalRing.residue ↥A) ⟨_, h₂⟩ ∈ modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1),
        x0.ord (C0.residue ⟨g, hg⟩)
          = (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (a ^ p)).ord (⟨_, h₂F⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))) :
    An.IsAttached C0 x0 := by
  haveI : NeZero (1 * p) := ⟨by rw [one_mul]; exact (Fact.out : p.Prime).ne_zero⟩

  obtain ⟨hzm, hzF, hzne, hzord⟩ := hzg
  obtain ⟨hzC, hzres⟩ := hunit0 z hzm hzne
  have hz1 : x0.ord (C0.residue ⟨z, hzC⟩) = 1 := by rw [hordres0 z hzC hzm hzF]; exact hzord
  subst hz
  refine ⟨hnodes0, hzC, hz1, ?_⟩

  exact slopeLaw_ssAnnulus_zeroChart_wide_aux p A hp5 (1 * p) rfl C0 x0 a ha ha2 hw An An.param rfl z' hmod ⟨hzm, hzne⟩
    (hzg'.elim fun h hh => ⟨h, hh.elim fun hF hr => hr.1⟩) hdom hunit0 hordres0

end
end P2MW.S_ModularCurve_isAttached_ssAnnulus_zeroChart_of_chartSpec_of_paramGauss_of_eq_zero_or_eq_ofNat1728_levelOne
