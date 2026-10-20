namespace P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard

set_option autoImplicit false

p2m_open

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian

noncomputable section

namespace WGenC

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (R' : Type u) [CommRing R'] [Algebra R R']

def prodMapIso (w : C ≅ C) (hw : w.hom ≫ c = c) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    pullback (baseChange R c R') t ≅ pullback (baseChange R c R') t where
  hom := WGenH.prodMap (endoBaseChange c R' ⟨w.hom, hw⟩) t
  inv := WGenH.prodMap (endoBaseChange c R' ⟨w.inv, by rw [Iso.inv_comp_eq, hw]⟩) t
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, WGenH.prodMap_fst, WGenH.prodMap_fst_assoc, Category.id_comp]
      apply pullback.hom_ext
      · simp only [Category.assoc, endoBaseChange_fst, endoBaseChange_fst_assoc, Iso.hom_inv_id, Category.comp_id]
      · rw [Category.assoc, Category.assoc, (endoBaseChange c R' _).2, (endoBaseChange c R' _).2]
    · simp only [Category.assoc, WGenH.prodMap_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, WGenH.prodMap_fst, WGenH.prodMap_fst_assoc, Category.id_comp]
      apply pullback.hom_ext
      · simp only [Category.assoc, endoBaseChange_fst, endoBaseChange_fst_assoc, Iso.inv_hom_id, Category.comp_id]
      · rw [Category.assoc, Category.assoc, (endoBaseChange c R' _).2, (endoBaseChange c R' _).2]
    · simp only [Category.assoc, WGenH.prodMap_snd, Category.id_comp]

end WGenC
end
end P2MW.S_ModularCurve_XHDRModelAtP_nonempty_poincare_pullbackAlong_pts_smul_iso_pullback_w_of_abelJacobiPin
