namespace P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne

attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField

set_option autoImplicit false

p2m_open

universe u

namespace ModularCurve

namespace JHNeronObjectAtP

namespace RedLambda

p2m_open

variable {p M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} {A : ValuationSubring (AlgebraicClosure ℚ)}

section Additive

variable (Λ : LevelData p M H hpM A) (hΛ : AbelianSchemePropertyBundle (baseRing p) Λ.f)
  (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
  (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
    Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))

noncomputable def redHom
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) :
    JH (M / p) (infSubgroup p M H hpM) →+ Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  AddMonoidHom.mk' (red Λ hΛ) (red_add Λ hΛ hΛpts_add hΛptsSp_add)

end Additive
end RedLambda
end JHNeronObjectAtP
end ModularCurve
end P2MW.S_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
