namespace P2MW.S_ModularCurve_pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel

attribute [-instance] AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

universe u v

set_option autoImplicit false

p2m_open

noncomputable section

p2m_open

noncomputable section

p2m_open

namespace PTSQProof

noncomputable section

section RelFacts

variable {R₀ : Type} [CommRing R₀] {C₁ C₂ : Scheme.{0}}
  {c₁ : C₁ ⟶ Spec (CommRingCat.of R₀)} {c₂ : C₂ ⟶ Spec (CommRingCat.of R₀)}
  (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₀))) c₂)

variable {ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₀))) c₁} (e : C₁ ≅ C₂) (he' : e.inv ≫ c₁ = c₂)

theorem cut_pullback_curveChange {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R₀)}
    (M : RigidifiedLineBundle c₁ ε₁ t) (hM : FibrewiseAlgEquivZero M)
    (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T) :
    IsAlgEquivZero (fibreAt c₂ t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c₂ t) s)).obj
      ((Scheme.Modules.pullback (curveChange (c := c₁) (c' := c₂) e.inv he' t)).obj M.L)) := by
  let f := curveChange (c := c₁) (c' := c₂) e.inv he' t
  let e' : Limits.pullback (pullback.snd c₂ t) s ⟶ Limits.pullback (pullback.snd c₁ t) s :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 T) (by rw [Category.comp_id]; exact (curveChange_snd e.inv he' t).symm) (by simp)
  have he'' : e' ≫ fibreAt c₁ t s = fibreAt c₂ t s := by
    simp only [e', fibreAt, pullback.lift_snd, Category.comp_id]
  have hfst : e' ≫ pullback.fst (pullback.snd c₁ t) s = pullback.fst (pullback.snd c₂ t) s ≫ f := by
    simp only [e', pullback.lift_fst]
  refine IsAlgEquivZero.of_iso ?_ ((hM k s).pullback e' he'')
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫ ((Scheme.Modules.pullbackComp _ _).app M.L).symm

end RelFacts
end
end PTSQProof
end
end
end P2MW.S_ModularCurve_pts_lift_comp_theta_fst_eq_pts_of_dRModelPackage_of_igusaModel
