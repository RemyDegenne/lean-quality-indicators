namespace P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv

set_option autoImplicit false

universe u

open ModularCurve

namespace P2M

namespace RelWeilZar

open WeierstrassCurve MvPolynomial

section Rule

variable (ℓ : ℕ)

theorem isUnit_Δ_map_Wu {Ω : Type u} [CommRing Ω] (φ : Ru.{u} ℓ →+* Ω) : IsUnit ((Wu ℓ).map φ).Δ := by
  rw [WeierstrassCurve.map_Δ]; exact (isUnit_Δ_Wu ℓ).map φ

end Rule
end RelWeilZar
end P2M
end P2MW.S_ModularCurve_LevelComponent_exists_not_mem_and_exists_pow_eq_one_forall_weilPairing0_toPoint_mapRing_localizationAway_eq
