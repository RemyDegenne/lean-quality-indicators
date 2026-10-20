namespace P2MW.S_ModularCurve_PlaceSpecialization_red_eq_zero_of_isCuspidal_of_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 3200000

p2m_open

noncomputable section

p2m_open

namespace ModularCurve

namespace PlaceSpecialization

namespace LevelOneProlongationPair

p2m_open

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

theorem exists_coords_of_isStrictTypeOne
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : P.IsStrictTypeOne W) :
    ∃ x y : A,
      0 < W.ord ((jFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (x : AlgebraicClosure ℚ)) ∧
      0 < W.ord ((jqFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (y : AlgebraicClosure ℚ)) ∧
      P.redFst W = charLGeomPlaceOfPoint k (red x) ∧
      P.redSnd W = charLGeomPlaceOfPoint k (red y) ∧
      red y = red x ^ q ∧ red x ^ (q ^ 2) ≠ red x := by
  letI := Classical.decEq (RatFunc k)

  have hinf_fix := ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty k data hKr

  have hJα : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jFun (q := q) := Subtype.ext (coe_heckeAlphaBar 1 q _)
  have hJβ : heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jqFun (q := q) := by
    apply Subtype.ext
    rw [coe_heckeBetaBar]
    show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
    simp only [coeffEmb, ModularCurve.coeffMap_qExpand, one_mul]

  have hx : ∃ x : A, 0 < W.ord ((jFun (q := q))
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) := by
    by_contra hno
    push_neg at hno
    have h1 := P.redFst_eq_placeInfty_of_forall_ord_le_zero W hno
    exact hW.2 (by rw [h1, hinf_fix, hinf_fix])
  obtain ⟨x, hx⟩ := hx
  have hredFst : P.redFst W = charLGeomPlaceOfPoint k (red x) :=
    P.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos W x (by rw [hJα]; exact hx)

  have hy : ∃ y : A, 0 < W.ord ((jqFun (q := q))
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)) := by
    by_contra hno
    push_neg at hno
    have h2 : P.redSnd W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by
      refine P.sp_eq_placeInfty_of_forall_ord_le_zero _ fun b => ?_
      have h := hno b
      rw [← hJβ, ← (heckeBetaBar (AlgebraicClosure ℚ) 1 q).commutes (b : AlgebraicClosure ℚ), ← map_sub,
        Place.ord_restrictAlong _ hβ] at h
      have hepos : 0 < (Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) W : ℤ) := by
        letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
        haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
        haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
        exact_mod_cast Place.ramificationIndex_pos (F := modularFunctionFieldBar 1) W
      by_contra hpos
      push_neg at hpos
      exact absurd h (not_le.mpr (mul_pos hepos hpos))
    have h3 : P.redFst W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) :=
      frobOnPlacesGeomLevel_injective k 1 data hKr (by rw [hinf_fix]; exact hW.1.trans h2)
    exact hW.2 (by rw [h3, hinf_fix, hinf_fix])
  obtain ⟨y, hy⟩ := hy
  have hredSnd : P.redSnd W = charLGeomPlaceOfPoint k (red y) :=
    P.redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos W y (by rw [hJβ]; exact hy)

  have G5 : ∀ a : k, frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)
      = charLGeomPlaceOfPoint k (a ^ q) := pinN_G5 (k := k) data hKr

  have hyx : red y = red x ^ q := by
    have h := hW.1
    rw [hredFst, hredSnd, G5] at h
    exact (charLGeomPlaceOfPoint_injective k h).symm
  have hfix : red x ^ (q ^ 2) ≠ red x := by
    intro he
    apply hW.2
    rw [hredFst, G5, G5, ← pow_mul, show q * q = q ^ 2 from (sq q).symm, he]
  exact ⟨x, y, hx, hy, hredFst, hredSnd, hyx, hfix⟩

end LevelOneProlongationPair
end PlaceSpecialization
end ModularCurve
end
end P2MW.S_ModularCurve_PlaceSpecialization_red_eq_zero_of_isCuspidal_of_coeffEmb_modularUnitSeries_inv_sub_algebraMap_mem_nonunits
